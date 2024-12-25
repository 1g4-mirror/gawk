/*
 * Copyright (C) 2023, 2024, Arnold David Robbins.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
 * TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#include <assert.h>
#include <stdio.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <wctype.h>
#include <wchar.h>
#include <locale.h>
#include "charset.h"	// for the charset_t typedef

#define INITIAL_ALLOCATION 10
#define MAX_CODE_POINT 0x10ffff	// max Unicode code point

typedef struct set_item {
	enum set_item_type {
		CTYPE_ITEM,
		RANGE_ITEM,
	} item_type;
	union {
		struct _ctype {
			wctype_t    wtype;
			const char *type_name;
		} c;
		struct _range {
			int32_t start, end;
		} r;
	} u;
} set_item;
#define wtype		u.c.wtype
#define type_name	u.c.type_name
#define start		u.r.start
#define end			u.r.end
struct _charset {
	bool     complemented;      // For [^...] sets
	bool     no_newlines;       // If \n can't be in the set
	bool     finalized;         // No more changes possible
	size_t   nchars_inuse;      // Number of characters used
	size_t   nchars_allocated;  // Number of characters allocated
	int32_t  *chars;            // Characters added to the set
	size_t   nelems;            // Number of elements (items) in use
	size_t   allocated;         // Number allocated
	set_item *items;            // Array of items
};
/* item_compare_for_searching --- compare two set_items */

static int
item_compare_for_searching(const void *k, const void *e)
{
	set_item *thekey = (set_item *) k;
	set_item *elem = (set_item *) e;

	assert(thekey->item_type == RANGE_ITEM && elem->item_type == RANGE_ITEM);

	if (elem->start <= thekey->start && thekey->start <= elem->end)
		return 0;	// found it
	else if (thekey->end < elem->start)
		return -1;
	else {
		assert(thekey->start > elem->end);
		return 1;
	}
}
/* wint_compare --- compare two wint values for qsort */

static int
wint_compare(const void *l, const void *r)
{
	wint_t *left = (wint_t *) l;
	wint_t *right = (wint_t *) r;

	return *left - *right;
}
/* item_compare_for_sorting --- compare two set_items */

static int
item_compare_for_sorting(const void *l, const void *r)
{
	set_item *left = (set_item *) l;
	set_item *right = (set_item *) r;

	if (left->item_type == CTYPE_ITEM && right->item_type == CTYPE_ITEM) {
		return left->wtype - right->wtype;
	} else if (left->item_type == CTYPE_ITEM && right->item_type == RANGE_ITEM) {
		return -1;
	} else if (left->item_type == RANGE_ITEM && right->item_type == CTYPE_ITEM) {
		return +1;
	} else {
		assert(left->item_type == RANGE_ITEM && right->item_type == RANGE_ITEM);
		return left->start - right->start;
	}
}

/* is_found --- return true if the character is found */

static bool
is_found(const charset_t *set, int32_t the_char)
{
	set_item *items = set->items;
	int i;

	if (set->items == NULL)		// empty set, can't match
		return false;
	if (set->nelems == 1 && set->items[0].item_type == RANGE_ITEM) {
	    return (set->items[0].start <= the_char && the_char <= set->items[0].end);
	}
	for (i = 0; i < set->nelems; i++) {
		// linear search of ctype items
		if (items[i].item_type == RANGE_ITEM)
			break;
	
		assert(items[i].item_type == CTYPE_ITEM);
		if (iswctype(the_char, items[i].wtype))
			return true;
	}
	
	if (i >= set->nelems)
		return false;
	assert(items[i].item_type == RANGE_ITEM);
	
	// binary search to see if we have it
	set_item *found;
	set_item key;
	key.item_type = RANGE_ITEM;
	key.start = key.end = the_char;
	
	found = bsearch(& key, set->items + i, set->nelems - i,
					sizeof(set_item), item_compare_for_searching);
	
	return found != NULL;
}
/* finalize --- condense all the info into the final data structure */

static void
finalize(charset_t *set)
{
	assert(set != NULL);
	int result = 0;

	qsort(set->chars, set->nchars_inuse, sizeof(wint_t), wint_compare);
	size_t i, j;
	for (i = 0, j = 1; j < set->nchars_inuse; i++, j++) {
		if (set->chars[i] == set->chars[j]) {
			for (int k = j + 1; k < set->nchars_inuse; j++, k++) {
				set->chars[j] = set->chars[k];
			}
			set->chars[j] = L'\0';
	
			set->nchars_inuse--;
			j = i;
			i--;	// keep searching from same spot
		}
	}
	if (set->chars != NULL)
		set->chars[set->nchars_inuse] = L'\0';	// not strictly necessary, but doesn't hurt
	size_t range_start, total;
	range_start = total = 0;
	for (i = 0, j = 1; j < set->nchars_inuse; i++, j++) {
		if (set->chars[j] == set->chars[i] + 1) {	// ab...
			continue;
		} else if (set->chars[j] > set->chars[i] + 1) {
			// acd...
			// push a and start next range at c
			result = charset_add_range(set, set->chars[range_start], set->chars[i]);
			if (result != CSET_SUCCESS)
				return;
			total++;
			range_start = j;
		}
	}
	// Get any final range or character
	if (set->nchars_inuse > 0 && range_start <= set->nchars_inuse - 1) {
		result = charset_add_range(set, set->chars[range_start],
					set->chars[set->nchars_inuse-1]);
		if (result != CSET_SUCCESS)
			return;
		total++;
	}
	set->nchars_inuse = total;
	// sort it
	qsort(set->items, set->nelems,
			sizeof(set_item), item_compare_for_sorting);
	
	// condense it
	set_item *items = set->items;
	for (i = 0, j = 1; j < set->nelems; i++, j++) {
		if (   items[i].item_type == CTYPE_ITEM
			&& items[j].item_type == CTYPE_ITEM
			&& items[i].wtype == items[j].wtype) {
			free((void *) items[j].type_name);
			for (int k = j + 1; k < set->nelems; j++, k++)
				items[j] = items[k];
			
			set->nelems--;
			i--;	// compensate for loop, continue checking at current position
			j = i + 1;
		} else if (items[i].item_type != items[j].item_type) {
			continue;
		} else if (items[i].item_type == RANGE_ITEM) {
			bool need_shift = false;
			if (items[i].start == items[j].start && items[i].end == items[j].end) {
				need_shift = true;
			} else if (items[i].end + 1 == items[j].start) {
				items[i].end = items[j].end;
				need_shift = true;
			} else if (items[i].start < items[j].start && items[i].end > items[j].end) {
				need_shift = true;
			} else if (   items[i].start <= items[j].start
			           && items[i].end > items[j].start
			           && items[j].end >= items[i].end) {
				items[i].end = items[j].end;
				need_shift = true;
			}
			if (need_shift) {
				for (int k = j + 1; k < set->nelems; j++, k++)
					items[j] = items[k];
				
				set->nelems--;
				i--;	// compensate for loop, continue checking at current position
				j = i + 1;
			}
			// otherwise, just continue around the loop
		}
	}
	set->finalized = true;
}
/* charset_create --- make a new charset_t and initialize it */

charset_t *
charset_create(int *errcode)
{
	if (errcode == NULL)
		return NULL;

	charset_t *set = (charset_t *) malloc(sizeof(charset_t));
	if (set == NULL) {
		*errcode = CSET_ESPACE;
		return NULL;
	}

	memset(set, 0, sizeof(charset_t));

	*errcode = CSET_SUCCESS;
	return set;
}
/* charset_add_char --- add a single wide character to the set */

int
charset_add_char(charset_t *set, int32_t wc)
{
	if (set == NULL)
		return CSET_EBADPTR;
	if (set->finalized)
		return CSET_EFROZEN;

	if (wc < 0)
		return CSET_ERANGE;

	if (set->chars == NULL) {
		set->chars = (int32_t *) malloc(sizeof(int32_t) * INITIAL_ALLOCATION);
		if (set->chars == NULL)
			return CSET_ESPACE;
	
		set->nchars_allocated = INITIAL_ALLOCATION;
		set->nchars_inuse = 0;
	} else if (set->nchars_inuse + 1 >= set->nchars_allocated) {
		int new_amount = set->nchars_allocated * 2;
		int32_t *new_data = (int32_t *) realloc(set->chars, new_amount * sizeof(int32_t));
	
		if (new_data == NULL)
			return CSET_ESPACE;
	
		memset(new_data + set->nchars_allocated, 0, set->nchars_allocated * sizeof(int32_t));
		set->nchars_allocated = new_amount;
		set->chars = new_data;
	}

	set->chars[set->nchars_inuse++] = wc;
	set->chars[set->nchars_inuse] = L'\0';	// make it into a string

	return CSET_SUCCESS;
}
/* charset_add_range --- add a range item */

int
charset_add_range(charset_t *set, int32_t first, int32_t last)
{
	if (set == NULL)
		return CSET_EBADPTR;
	if (set->finalized)
		return CSET_EFROZEN;

	if (first < 0 || last < 0 || first > last)
		return CSET_ERANGE;

	if (set->items == NULL) {
		set->items = (set_item *) malloc(sizeof(set_item) * INITIAL_ALLOCATION);
		if (set->items == NULL)
			return CSET_ESPACE;
	
		set->allocated = INITIAL_ALLOCATION;
		set->nelems = 0;
	} else if (set->nelems + 1 >= set->allocated) {
		int new_amount = set->allocated * 2;
		set_item *new_data = (set_item *) realloc(set->items, new_amount * sizeof(set_item));
	
		if (new_data == NULL)
			return CSET_ESPACE;
	
		memset(new_data + set->allocated, 0, set->allocated * sizeof(set_item));
		set->allocated = new_amount;
		set->items = new_data;
	}

	set_item new_item;
	new_item.item_type = RANGE_ITEM;
	new_item.start = first;
	new_item.end = last;
	set->items[set->nelems++] = new_item;

	return CSET_SUCCESS;
}
/* charset_invert --- mark charset to return success if requested character not found */

int
charset_invert(charset_t *set)
{
	if (set == NULL)
		return CSET_EBADPTR;
	if (set->finalized)
		return CSET_EFROZEN;

	set->complemented = true;
	return CSET_SUCCESS;
}
/* charset_set_no_newline --- set the value of the "no newlines" flag */

int charset_set_no_newlines(charset_t *set, bool no_newlines)
{
	if (set == NULL)
		return CSET_EBADPTR;
	if (set->finalized)
		return CSET_EFROZEN;

	set->no_newlines = no_newlines;
	return CSET_SUCCESS;
}
/* charset_add_cclass --- add a character class, like "alnum" */

int
charset_add_cclass(charset_t *set, const char *cclass)
{
	if (set == NULL)
		return CSET_EBADPTR;
	if (set->finalized)
		return CSET_EFROZEN;

	if (set->items == NULL) {
		set->items = (set_item *) malloc(sizeof(set_item) * INITIAL_ALLOCATION);
		if (set->items == NULL)
			return CSET_ESPACE;
	
		set->allocated = INITIAL_ALLOCATION;
		set->nelems = 0;
	} else if (set->nelems + 1 >= set->allocated) {
		int new_amount = set->allocated * 2;
		set_item *new_data = (set_item *) realloc(set->items, new_amount * sizeof(set_item));
	
		if (new_data == NULL)
			return CSET_ESPACE;
	
		memset(new_data + set->allocated, 0, set->allocated * sizeof(set_item));
		set->allocated = new_amount;
		set->items = new_data;
	}

	wctype_t the_type = wctype(cclass);
	if (the_type == 0)	// not a known class name
		return CSET_ECTYPE;

	const char *class_name = strdup(cclass);
	if (class_name == NULL)
		return CSET_ESPACE;

	set_item new_item;
	new_item.item_type = CTYPE_ITEM;

	new_item.wtype = the_type;
	new_item.type_name = class_name;
	set->items[set->nelems++] = new_item;

	return CSET_SUCCESS;
}
/* charset_add_equiv --- add an equivalence class */

int
charset_add_equiv(charset_t *set, int32_t equiv)
{
	if (set == NULL)
		return CSET_EBADPTR;
	if (set->finalized)
		return CSET_EFROZEN;

	if (equiv < 0)
		return CSET_ERANGE;

	wchar_t wcs_in[2];
	wchar_t wcs[2];
	wchar_t abuf[100], wbuf[100];
	int result;

	wcs_in[0] = equiv;
	wcs_in[1] = 0;
	wcsxfrm(abuf, wcs_in, 99);
	wcs[1] = 0;
	for (wchar_t u = 1; u <= MAX_CODE_POINT; ++u) {
		wcs[0] = u;
		wcsxfrm(wbuf, wcs, 99);
		if (abuf[0] == wbuf[0])
			if ((result = charset_add_char(set, u)) != CSET_SUCCESS)
				return result;
	}

	return CSET_SUCCESS;
}
/* charset_add_collate --- add a collating sequence */

int
charset_add_collate(charset_t *set, const int32_t *collate)
{
	if (set == NULL)
		return CSET_EBADPTR;
	if (set->finalized)
		return CSET_EFROZEN;

	// only single character collating sequences allowed,
	// at least right now
	if (collate[1] != L'\0')
		return CSET_ECOLLATE;

	return charset_add_char(set, collate[0]);
}
/* charset_in_set --- see if a character is in the set */

bool
charset_in_set(const charset_t *set, int32_t the_char)
{
	if (set == NULL || the_char < 0)
		return false;

	if (! set->finalized) {
		finalize((charset_t *) set);

		if (! set->finalized)	// finalize() failed
			return false;
	}

	if (the_char == L'\n' && set->no_newlines && set->complemented)
		return false;

	bool found = is_found(set, the_char);
	if (set->complemented)
		found = ! found;		// reverse sense of the match

	return found;
}
/* charset_free --- free all storage */

int
charset_free(const charset_t *set)
{
	if (set == NULL)
		return CSET_EBADPTR;
	// no need to check for finalized

	if (set->items != NULL) {
		for (int i = 0; i < set->nelems; i++) {
			if (set->items[i].item_type == CTYPE_ITEM)
				free((void *) set->items[i].type_name);
			else
				break;
		}
		free((void *) set->items);
	}

	if (set->chars != NULL)
		free((void *) set->chars);

	free((void *) set);

	return CSET_SUCCESS;
}
/* charset_dump --- dump out the data structures */

void
charset_dump(const charset_t *set, FILE *fp)
{
	static const char *boolval[] = {
		"false",
		"true",
	};

	if (set == NULL || fp == NULL)
		return;

	fprintf(fp, "complemented = %s\n", boolval[!! set->complemented]);
	fprintf(fp, "no_newlines = %s\n", boolval[!! set->no_newlines]);
	fprintf(fp, "finalized = %s\n", boolval[!! set->finalized]);

	set_item *items = set->items;
	for (int i = 0; i < set->nelems; i++) {
		if (items[i].item_type == CTYPE_ITEM) {
			fprintf(fp, "%3d. CTYPE: [:%s:]\n", i, items[i].type_name);
			continue;
		}
		assert(items[i].item_type == RANGE_ITEM);
		fprintf(fp, "%3d. RANGE: start = L'%lc', end = L'%lc'\n",
			i, items[i].start, items[i].end);
	}
	fflush(fp);
}
