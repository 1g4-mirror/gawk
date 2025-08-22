//
// MinRX: a minimal matcher for POSIX Extended Regular Expressions.
// Copyright (C) 2023, 2024, 2025 Michael J. Haertel.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions
// are met:
//
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS “AS IS” AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
// OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
// HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
// LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
// OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
// SUCH DAMAGE.

#include <ctype.h>
#include <langinfo.h>
#include <limits.h>
#include <locale.h>
#include <memory.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <wctype.h>

#include "charset.h"

#include "minrx.h"

#ifdef __GNUC__
#define INLINE __attribute__((__always_inline__)) inline
#else
#define INLINE inline
#endif

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif /* HAVE_CONFIG_H */

#ifdef HAVE_GETTEXT_H
#include <gettext.h>
#define _(msgid)  gettext(msgid)
#else /* ! HAVE_GETTEXT_H */
#define _(msgid)  msgid
#endif /* ! HAVE_GETTEXT_H */

#define N_(msgid) msgid

/////////////////// Character conversion functions from class WConv //////////////////

typedef int32_t WChar;			// because wchar_t may not be 32 bits

// anonymous constants
enum {
	WCharMax = 0x10FFFF,	// maximum code point: valid for Unicode and (FIXME!) blithely assumed for non-Unicode
	WConv_End = -1,
};
typedef enum Encoding { Encoding_Byte, Encoding_MBtoWC, Encoding_UTF8 } Encoding;

typedef struct WConv {
	WChar (*nextfn)();
	char *bp;
	char *ep;
	char *cp;
	mbstate_t mbs;
} WConv;

static INLINE size_t wc_off(WConv *this) { return this->cp - this->bp; }
static INLINE char *wc_ptr(WConv *this) { return this->cp; }
static INLINE char *wc_save(WConv *this) { return this->cp; }
static INLINE void wc_restore(WConv *this, const char *p) { this->cp = (char *) p; }

static INLINE WChar wc_nextchr(WConv *this) { return (*(this->nextfn))(); }
static INLINE WChar wc_nextbyte(WConv *this) { return this->cp != this->ep ? (unsigned char) *(this->cp++) : (WChar) WConv_End; }
static INLINE WChar wc_lookahead(WConv *this) { return wc_nextchr(this); }

static WChar wc_nextmbtowc(WConv *this)
{
	wchar_t wct = L'\0';
	if (this->cp != this->ep) {
		size_t n = mbrtowc(&wct, this->cp, this->ep - this->cp, & this->mbs);
		if (n == 0 || n == (size_t) -1 || n == (size_t) -2) {
			if (wct == L'\0')
				wct = INT_MIN + (unsigned char) *(this->cp++);
		} else {
			this->cp += n;
		}
		return wct;
	} else {
		return WConv_End;
	}
}

static WChar wc_nextutf8(WConv *this)
{
	if (this->cp != this->ep) {
		WChar u = (unsigned char) this->cp[0];
		if (u < 0x80)
			return this->cp += 1, u;
		if ((u & 0x40) == 0 || this->cp + 1 == this->ep)
		error:
			return this->cp += 1, INT_MIN + u;
		WChar v = (unsigned char) this->cp[1];
		if ((v & 0xC0) != 0x80)
			goto error;
		if ((u & 0x20) == 0) {
			WChar r = ((u & 0x1F) << 6) | (v & 0x3F);
			if (r < 0x80)
				goto error;
			return this->cp += 2, r;
		}
		if (this->cp + 2 == this->ep)
			goto error;
		WChar w = (unsigned char) this->cp[2];
		if ((w & 0xC0) != 0x80)
			goto error;
		if ((u & 0x10) == 0) {
			WChar r = ((u & 0x0F) << 12) | ((v & 0x3F) << 6) | (w & 0x3F);
			if (r < 0x800)
				goto error;
			return this->cp += 3, r;
		}
		if (this->cp + 3 == this->ep)
			goto error;
		WChar x = (unsigned char) this->cp[3];
		if ((x & 0xC0) != 0x80)
			goto error;
		if ((u & 0x08) != 0)
			goto error;
		WChar r = ((u & 0x07) << 18) | ((v & 0x3F) << 12) | ((w & 0x3F) << 6) | (x & 0x3F);
		if (r < 0x010000 || r > 0x10FFFF)
			goto error;
		return this->cp += 4, r;
	} else {
		return WConv_End;
	}
}

WChar (*nextfns[3])() = { & wc_nextbyte, & wc_nextmbtowc, & wc_nextutf8 };

static WConv *wc_make_n(Encoding e, const char *bp, const char *ep)
{
	WConv *wconv = calloc(1, sizeof(WConv));
	if (wconv == NULL)
		return NULL;

	wconv->nextfn = nextfns[(int) e];
	wconv->bp = (char *) bp;
	wconv->ep = (char *) ep;
	memset(& wconv->mbs, 0, sizeof wconv->mbs);

	return wconv;
}

static INLINE WConv *wc_make(Encoding e, const char *bp)
{
	return wc_make_n(e, bp, bp + strlen(bp));
}

/////////////////// Character set struct and functions from class CSet //////////////////

typedef charset_t *CSet;

static INLINE CSet cset_create(Encoding enc)
{
	int errcode = 0;
	CSet charset;

	charset = charset_create(& errcode, MB_CUR_MAX, enc == Encoding_UTF8);

	return charset;
}

static INLINE CSet cset_merge(CSet lhs, CSet rhs)
{
	charset_merge(lhs, rhs);

	return lhs;
}

static INLINE void cset_free(CSet charset) { if (charset) { charset_free(charset); } }

static INLINE CSet cset_invert(CSet charset)
{
	int errcode = 0;

	charset_t *newset = charset_invert(charset, &errcode); // FIXME: no error checking
	charset_free(charset);

	return newset;
}

static INLINE CSet cset_set(CSet charset, WChar wclo, WChar wchi)
{
	charset_add_range(charset, wclo, wchi);	// FIXME: no error checking

	return charset;
}

static INLINE CSet cset_setone(CSet charset, WChar wc)
{
	charset_add_char(charset, wc);	// FIXME: no error checking

	return charset;
}

static INLINE bool cset_test(CSet charset, WChar wc)
{
	return charset_in_set(charset, wc);
}

static INLINE bool cset_cclass(CSet charset, minrx_regcomp_flags_t flags, Encoding enc, const char *name)
{
	int result = charset_add_cclass(charset, name);
	if ((flags & MINRX_REG_ICASE) != 0) {
		if (strcmp(name, "lower") == 0)
			charset_add_cclass(charset, "upper");	// FIXME: Add error checking
		else if (strcmp(name, "upper") == 0)
			charset_add_cclass(charset, "lower");	// FIXME: Add error checking
	}
	return result == CSET_SUCCESS;
}

static const char *temp_string(const char *bp, const char *ep)
{
	static char buffer[100];	// FIXME: no arbitrary limits;
	char *cp = buffer;

	for (int i = 0; i < sizeof(buffer)-1 && bp < ep; i++) {
		*cp++ = *bp++;
	}

	*cp++ = '\0';

	return buffer;
}

static INLINE void cset_add_equiv(CSet charset, int32_t equiv)
{
	wchar_t wcs_in[2];
	wchar_t wcs[2];
	wchar_t abuf[100], wbuf[100];

	wcs_in[0] = equiv;
	wcs_in[1] = 0;
	wcsxfrm(abuf, wcs_in, 99);
	wcs[1] = 0;
	for (wchar_t u = 1; u <= WCharMax; ++u) {
		wcs[0] = u;
		wcsxfrm(wbuf, wcs, 99);
		if (abuf[0] == wbuf[0])
			cset_setone(charset, u);
	}
}

static INLINE unsigned int utfprefix(WChar wc)
{
	if (wc < 0x80)
		return wc;
	if (wc < 0x800)
		return 0xC0 + (wc >> 6);
	if (wc < 0x10000)
		return 0xE0 + (wc >> 12);
	if (wc < 0x100000)
		return 0xF0 + (wc >> 18);
	return 0xF4;
}

static minrx_result_t cset_parse(CSet charset, minrx_regcomp_flags_t flags, Encoding enc, WConv *wconv)
{
	WChar wc = wc_nextchr(wconv);
	bool inv = (wc == L'^');
	if (inv)
		wc = wc_nextchr(wconv);
	for (bool first = true; first || wc != L']'; first = false) {
		if (wc == WConv_End)
			return MINRX_REG_EBRACK;
		WChar wclo = wc, wchi = wc;
		wc = wc_nextchr(wconv);
		if (wclo == L'\\' && (flags & MINRX_REG_BRACK_ESCAPE) != 0) {
			if (wc != WConv_End) {
				wclo = wchi = wc;
				wc = wc_nextchr(wconv);
			} else {
				return MINRX_REG_EESCAPE;
			}
		} else if (wclo == L'[') {
			if (wc == L'.') {
				wc = wc_nextchr(wconv);
				wclo = wchi = wc;
				int32_t coll[2] = { wc, L'\0' };
				charset_add_collate(charset, coll);	// FIXME: No error checking
				if ((flags & MINRX_REG_ICASE) != 0) {
					if (iswlower(wc))
						coll[0] = towupper(wc);
					else if (iswupper(wc))
						coll[0] = towlower(wc);
					charset_add_collate(charset, coll);	// FIXME: No error checking
				}
				wc = wc_nextchr(wconv);
				if (wc != L'.' || (wc = wc_nextchr(wconv)) != L']')
					return MINRX_REG_ECOLLATE;
				wc = wc_nextchr(wconv);
			} else if (wc == L':') {
				char *bp, *ep;
				bp = ep = wc_ptr(wconv);
				do
					ep = wc_ptr(wconv), wc = wc_nextchr(wconv);
				while (wc != WConv_End && wc != L':');
				if (wc != L':')
					return MINRX_REG_ECTYPE;
				wc = wc_nextchr(wconv);
				if (wc != L']')
					return MINRX_REG_ECTYPE;
				wc = wc_nextchr(wconv);
				const char *cclname = temp_string(bp, ep);
				if (cset_cclass(charset, flags, enc, cclname))
					continue;
				return MINRX_REG_ECTYPE;
			} else if (wc == L'=') {
				wc = wc_nextchr(wconv);
				wclo = wchi = wc;
				charset_add_equiv(charset, wc);	// FIXME: No error checking
				if ((flags & MINRX_REG_ICASE) != 0) {
					if (iswlower(wc))
						charset_add_equiv(charset, towupper(wc));	// FIXME: no error checking
					else if (iswupper(wc))
						charset_add_equiv(charset, towlower(wc));	// FIXME: no error checking
				}
				wc = wc_nextchr(wconv);
				if (wc != L'=' || (wc = wc_nextchr(wconv)) != L']')
					return MINRX_REG_ECOLLATE;
			}
		}
		bool range = false;
		if (wc == L'-') {
			char *save = wc_save(wconv);
			wc = wc_nextchr(wconv);
			if (wc == WConv_End)
				return MINRX_REG_EBRACK;
			if (wc != L']') {
				wchi = wc;
				wc = wc_nextchr(wconv);
				if (wchi == L'\\' && (flags & MINRX_REG_BRACK_ESCAPE) != 0) {
					if (wc != WConv_End) {
						wchi = wc;
						wc = wc_nextchr(wconv);
					} else {
						return MINRX_REG_EESCAPE;
					}
				} else if (wchi == L'[') {
					if (wc == L'.') {
						wchi = wc_nextchr(wconv);
						wc = wc_nextchr(wconv);
						if (wc != L'.' || (wc = wc_nextchr(wconv)) != L']')
							return MINRX_REG_ECOLLATE;
						wc = wc_nextchr(wconv);
					} else if (wc == L':' || wc == L'=') {
						return MINRX_REG_ERANGE; // can't be range endpoint
					}
				}
				range = true;
			} else {
				wc_restore(wconv, save);
				wc = L'-';
			}
		}
		if (wclo > wchi || (wclo != wchi && (wclo < 0 || wchi < 0)))
			return MINRX_REG_ERANGE;
		if (wclo >= 0) {
			cset_set(charset, wclo, wchi);
			if ((flags & MINRX_REG_ICASE) != 0) {
				for (WChar wc = wclo; wc <= wchi; ++wc) {
					cset_setone(charset, enc == Encoding_Byte ? tolower(wc) : towlower(wc));
					cset_setone(charset, enc == Encoding_Byte ? toupper(wc) : towupper(wc));
				}
			}
		}
		if (range && wc == L'-' && wc_lookahead(wconv) != L']')
			return MINRX_REG_ERANGE;
	}
	if (inv) {
		if ((flags & MINRX_REG_NEWLINE) != 0)
			cset_setone(charset, L'\n');
		charset = cset_invert(charset);
	}
	return MINRX_REG_SUCCESS;
}

// First Unique stuff...

typedef struct {
	bool bytes[256];
	bool present;		// true if firstunique is set
	short firstunique;
} FirstUnique;

static FirstUnique fu_make(const bool fb[MAX_FIRSTBYTES])
{
	int n = 0, u = -1;
	FirstUnique result;

	memcpy(result.bytes, fb, MAX_FIRSTBYTES);
	result.firstunique = -1;
	result.present = false;

	for (int i = 0; i < MAX_FIRSTBYTES; ++i)
		if (fb[i])
			++n, u = i;

	if (n == 1) {
		result.present = true;
		result.firstunique = u;
	}

	return result;
}

static FirstUnique cset_firstbytes(CSet charset, Encoding e)
{
	FirstUnique result = { { '\0', }, '\0' };
	int errcode = 0;
	charset_firstbytes_t bytes;

	switch (e) {
	case Encoding_Byte:
	case Encoding_UTF8:
		bytes = charset_firstbytes(charset, & errcode);
		result = fu_make(bytes.bytes);
		break;
	default:
		break;
	}
	return result;
}

/////////////////// QSet struct and functions //////////////////

typedef struct QSet {
	uint64_t *bits[10];
	uint64_t bits0;
	uint64_t *bitsfree;
	int depth;
} QSet;

static QSet *qset_make(size_t limit)
{
	QSet *qset = (QSet *) calloc(1, sizeof(QSet));

	if (qset == NULL)
		return NULL;

	size_t s[10], t = 0;
	do
		t += (limit = s[qset->depth++] = (limit + 63u) / 64u);
	while (limit > 1);

	uint64_t *next = qset->bitsfree = (uint64_t *) malloc(t * sizeof(uint64_t));
	if (next == NULL) {
		free(qset);
		return NULL;
	}

	qset->bits[0] = & qset->bits0;
	for (int i = 1; i < qset->depth; ++i)
		qset->bits[i] = next, next += s[qset->depth - 1 - i];
	qset->bits0 = 0;

	return qset;
}

static INLINE void qset_free(QSet *qset) { if (qset->bitsfree) free(qset->bitsfree); }

static INLINE uint64_t bit(size_t k) { return (uint64_t) 1 << (k & 0x3F); }

static INLINE bool qset_empty(QSet *qset) { return ! qset->bits0; }

static INLINE bool qset_contains(const QSet *const qset, size_t k)
{
	int i = 0, s = 6 * qset->depth;
	size_t j = 0;
	while (i < qset->depth) {
		uint64_t x = qset->bits[i++][j];
		s -= 6;
		j = k >> s;
		uint64_t w = bit(j);
		if (!(x & w))
			return false;
	}
	return true;
}

static INLINE bool qset_insert(QSet *qset, size_t k)
{
	bool r = false;
	int i = 0, s = 6 * qset->depth;
	size_t j = 0;
	while (i < qset->depth) {
		int64_t *bp = & qset->bits[i++][j];
		int64_t x = *bp;
		s -= 6;
		j = k >> s;
		int64_t w = bit(j);
		if ((x & w) == 0) {
			if (i < qset->depth)
				 qset->bits[i][j] = 0;
			else
				r = true;
		}
		*bp = x | w;
	}
	return r;
}

// FIXME: Not sure this is exactly the right way to do this...
#define CTZ(x)	(sizeof(unsigned long long) == 8 ? __builtin_ctzll(x) : __builtin_ctzl(x))

static INLINE size_t qset_remove(QSet *qset)
{
	// caller must ensure !empty()
	size_t k = 0;
	int i = 0, d = qset->depth;
	do
		k = (k << 6) | CTZ(qset->bits[i++][k]);
	while (i != d);
	size_t r = k;
	do {
		--i;
		uint64_t w = bit(k);
		k >>= 6;
		if ((qset->bits[i][k] &= ~w) != 0)
			break;
	} while (i != 0);
	return r;
}

#if 0


namespace MinRX {


template <typename TYPE, TYPE INIT = 0>
struct COWVec {
	struct Storage;
	struct Allocator {
		std::size_t length;
		Storage *freelist = nullptr;
		Allocator(std::size_t length)
		: length(length)
		{}
		~Allocator() {
			for (Storage *s = freelist, *sfreelink = nullptr; s != nullptr; s = sfreelink) {
				sfreelink = s->u.freelink;
				::operator delete(s);
			}
		}
		Storage *alloc() {
			Storage *r;
			if (freelist) {
				r = freelist;
				freelist = r->u.freelink;
				r->u.allocator = this;
				r->refcnt = 1;
			} else {
				void *p = ::operator new(sizeof (Storage) + (length - 1) * sizeof (TYPE));
				r = new (p) Storage(*this);
			}
			for (std::size_t i = 0; i != length; ++i)
				(*r)[i] = INIT;
			return r;
		}
		void dealloc(Storage *s) {
			s->u.freelink = freelist;
			freelist = s;
		}
	};
	struct Storage {
		union {
			Allocator *allocator;
			Storage *freelink;
		} u;
		std::size_t refcnt;
		TYPE hack[1];
		const TYPE &operator[](std::size_t i) const { return (&hack[0])[i]; }
		TYPE &operator[](std::size_t i) { return (&hack[0])[i]; }
		Storage *clone() {
			auto s = u.allocator->alloc();
			for (std::size_t i = 0; i != u.allocator->length; ++i)
				(*s)[i] = (*this)[i];
			return s;
		}
		Storage(Allocator &a)
		: u({&a})
		, refcnt(1)
		{}
	};
	Storage *storage;
	COWVec(): storage(nullptr) {}
	COWVec(Allocator &a): storage(a.alloc()) {}
	COWVec(const COWVec &cv): storage(cv.storage) { ++storage->refcnt; }
	COWVec(COWVec &&cv): storage(cv.storage) { cv.storage = nullptr; }
	COWVec &operator=(const COWVec &cv) {
		++cv.storage->refcnt;
		if (storage && --storage->refcnt == 0)
			storage->u.allocator->dealloc(storage);
		storage = cv.storage;
		return *this;
	}
	COWVec &operator=(COWVec &&cv) {
		if (storage && --storage->refcnt == 0)
			storage->u.allocator->dealloc(storage);
		storage = cv.storage;
		cv.storage = nullptr;
		return *this;
	}
	~COWVec() { if (storage && --storage->refcnt == 0) storage->u.allocator->dealloc(storage); }
	auto cmp(std::size_t o, std::size_t n, const COWVec &other) const {
		const TYPE *xv = &(*storage)[0];
		const TYPE *yv = &(*other.storage)[0];
		for (std::size_t i = 0; i < n; i++)
			if (xv[o + i] != yv[o + i])
				return xv[o + i] <=> yv[o + i];
		return (TYPE) 0 <=> (TYPE) 0;
	}
	template <typename... XArgs>
	auto cmp(const COWVec &other, std::size_t limit, XArgs... xargs) const {
		std::size_t i;
		const TYPE *xv = &(*storage)[0];
		const TYPE *yv = &(*other.storage)[0];
		for (i = 0; i < limit - sizeof... (XArgs); i++)
			if (xv[i] != yv[i])
				return xv[i] <=> yv[i];
		if constexpr (sizeof...(XArgs) > 0)
			for (TYPE x : { xargs... })
				if (x != yv[i++])
					return x <=> yv[i - 1];
		return (TYPE) 0 <=> (TYPE) 0;
	}
	const TYPE &get(std::size_t idx) const { return (*storage)[idx]; }
	COWVec &put(std::size_t idx, TYPE val) {
		if ((*storage)[idx] == val)
			return *this;
		if (storage->refcnt > 1) {
			--storage->refcnt;
			storage = storage->clone();
			storage->refcnt = 1;
		}
		(*storage)[idx] = val;
		return *this;
	}
};


template <typename UINT, typename DATA>
struct QVec {
	QSet<UINT> qset;
	DATA *storage;
	QVec(UINT l): qset(l), storage(static_cast<DATA *>(::operator new(l * sizeof (DATA)))) {}
	~QVec() {
		clear();
		::operator delete(storage);
	}
	void clear() {
		while (!qset.empty()) {
			auto i = qset.remove();
			storage[i].~DATA();
		}
	}
	bool contains(UINT k) const { return qset.contains(k); }
	bool empty() const { return qset.empty(); }
	std::tuple<bool, DATA&> insert(UINT k, const DATA&) {
		bool newly = qset.insert(k);
		// WARNING: if newly inserted then we are returning a reference to uninitialized memory
		// and it is the caller's responsibility to construct valid DATA there.
		return {newly, storage[k]};
	}
	DATA &lookup(UINT k) { return storage[k]; }
	const DATA &lookup(UINT k) const { return storage[k]; }
	std::tuple<UINT, DATA> remove() {
		auto k = qset.remove();
		return {k, std::move(storage[k])};
	}
};



typedef std::size_t NInt;

struct Node {
	enum Type {
		// character-matching node types
		/* char <= uchar max */	// no args
		CSet = WCharMax + 1,	// args = index in Regexp::csets vector
		// epsilon-matching node types
		Exit,			// no args
		Fork,			// args = offset to first goto
		Goto,			// args = offset to next goto, offset to just after join
		Join,			// args = none (but supplies incoming stack depth for next node)
		Loop,			// args = offset to next, optional flag
		MinB,			// args = this minified subexpression nesting depth
		MinL,			// args = this minified subexpression nesting depth
		MinR,			// args = this minified subexpression nesting depth
		Next,			// args = offset to loop, infinite flag
		Skip,			// args = offset over skipped nodes
		SubL,			// args = minimum and maximum contained subexpression numbers
		SubR,			// args = minimum and maximum contained subexpression numbers
		ZBOB,			// no args - match empty string at beginning of buffer
		ZEOB,			// no args - match empty string at end of buffer
		ZBOL,			// no args - match empty string at beginning of buffer or following \n
		ZEOL,			// no args - match empty string at end of buffer or preceding \n
		ZBOW,			// no args - match empty string at beginning of word
		ZEOW,			// no args - match empty string at end of word
		ZXOW,			// no args - match empty string at either end of word
		ZNWB			// no args - match empty string at non-word-boundary
	};
	NInt type;
	NInt args[2];
	NInt nstk;
};

struct Regexp {
	WConv::Encoding enc;
	minrx_result_t err;
	const std::vector<CSet> csets;
	const std::vector<Node> nodes;
	std::optional<const CSet> firstcset;
	std::optional<const std::array<bool, 256>> firstbytes;
	std::optional<char> firstunique;
	std::size_t nmin;
	std::size_t nstk;
	std::size_t nsub;
};

struct Compile {
	const minrx_regcomp_flags_t flags;
	WConv::Encoding enc;
	WConv wconv;
	WChar wc;
	std::vector<CSet> csets;
	std::optional<std::size_t> dot;
	std::optional<std::size_t> esc_s;
	std::optional<std::size_t> esc_S;
	std::optional<std::size_t> esc_w;
	std::optional<std::size_t> esc_W;
	std::map<WChar, unsigned int> icmap;
	NInt nmin = 0;
	NInt nsub = 0;
	Compile(WConv::Encoding e, const char *bp, const char *ep, minrx_regcomp_flags_t flags): flags(flags), enc(e), wconv(e, bp, ep) { wc = wconv.nextchr(); }
	bool num(NInt &n, WChar &wc) {
		auto satmul = [](NInt x, NInt y) -> NInt {
			return (x == 0 || y == 0) ? 0 : ((x * y / x == y) ? x * y : -1);
		};
		if (wc < L'0' || wc > L'9')
			return false;
		NInt v = 0;
		do {
			v = satmul(v, 10);
			if (v == (NInt) -1 || (v += wc - L'0') < (NInt) wc - L'0') {
				do
					wc = wconv.nextchr();
				while (wc >= L'0' && wc <= L'9');
				n = -1;
				return true;
			}
			wc = wconv.nextchr();
		} while (wc >= L'0' && wc <= L'9');
		n = v;
		return true;
	}
	typedef std::tuple<std::deque<Node>, std::size_t, bool, minrx_result_t> Subexp;
	Subexp alt(bool nested, NInt nstk) {
		auto [lhs, lhmaxstk, lhasmin, err] = cat(nested, nstk);
		if (err)
			return {lhs, lhmaxstk, lhasmin, err};
		if (wc == L'|') {
			for (auto &l : lhs)
				l.nstk += 1;
			std::vector<Subexp> alts;
			while (wc == L'|') {
				wc = wconv.nextchr();
				alts.push_back(cat(nested, nstk + 1));
			}
			auto [rhs, rhmaxstk, rhasmin, err] = alts.back();
			if (err)
				return {rhs, rhmaxstk, rhasmin, err};
			rhs.push_front({Node::Goto, {rhs.size(), rhs.size() + 1}, nstk + 1});
			alts.pop_back();
			while (!alts.empty()) {
				auto [mhs, mhmaxstk, mhasmin, _] = alts.back();
				alts.pop_back();
				rhs.insert(rhs.begin(), mhs.begin(), mhs.end());
				rhmaxstk = std::max(mhmaxstk, rhmaxstk);
				rhasmin |= mhasmin;
				rhs.push_front({Node::Goto, {mhs.size(), rhs.size() + 1}, nstk + 1});
			}
			lhs.push_front({Node::Fork, { lhs.size(), 0 }, nstk + 1});
			lhs.insert(lhs.end(), rhs.begin(), rhs.end());
			lhmaxstk = std::max(lhmaxstk, rhmaxstk);
			lhasmin |= rhasmin;
			lhs.push_back({Node::Join, {lhs.size() - 1, 0}, nstk + 1});
		}
		return {lhs, lhmaxstk, lhasmin, MINRX_REG_SUCCESS};
	}
	Subexp cat(bool nested, NInt nstk) {
		auto [lhs, lhmaxstk, lhasmin, err] = rep(nested, nstk);
		if (err)
			return {lhs, lhmaxstk, lhasmin, err};
		while (wc != WConv::End && wc != L'|' && (wc != L')' || !nested)) {
			auto [rhs, rhmaxstk, rhasmin, err] = rep(nested, nstk);
			if (err)
				return {rhs, rhmaxstk, rhasmin, err};
			lhs.insert(lhs.end(), rhs.begin(), rhs.end());
			lhmaxstk = std::max(lhmaxstk, rhmaxstk);
			lhasmin |= rhasmin; 
		}
		return {lhs, lhmaxstk, lhasmin, MINRX_REG_SUCCESS};
	}
	Subexp minimize(const Subexp &lh, NInt nstk) {
		auto [nodes, maxstk, hasmin, err] = lh;
		for (auto &n : nodes)
			n.nstk += 1;
		nodes.push_front({Node::MinL, {0, 0}, nstk + 1});
		nodes.push_back({Node::MinR, {0, 0}, nstk});
		nmin = std::max(nmin, (std::size_t) 1);
		return {nodes, maxstk + 1, true, err};
	}
	void minraise(Subexp &lh) {
		auto &[nodes, maxstk, hasmin, err] = lh;
		NInt maxlevel = 0;
		for (auto &n : nodes)
			switch (n.type) {
			case Node::MinB:
			case Node::MinL:
			case Node::MinR:
				maxlevel = std::max(maxlevel, ++n.args[0]);
				break;
			default:
				;
			}
		nmin = std::max(nmin, maxlevel + 1);
	}
	Subexp mkrep(const Subexp &lh, bool optional, bool infinite, NInt nstk) {
		auto [lhs, lhmaxstk, lhasmin, _] = lh;
		if (optional && !infinite) {
			for (auto &l : lhs) l.nstk += 2;
			auto lhsize = lhs.size();
			lhs.push_front({Node::Skip, {lhsize, 0}, nstk + 2});
			return {lhs, lhmaxstk + 2, lhasmin, MINRX_REG_SUCCESS};
		} else {
			for (auto &l : lhs) l.nstk += 3;
			auto lhsize = lhs.size();
			lhs.push_front({Node::Loop, {lhsize, (NInt) optional}, nstk + 3});
			lhs.push_back({Node::Next, {lhsize, (NInt) infinite}, nstk});
			return {lhs, lhmaxstk + 3, lhasmin, MINRX_REG_SUCCESS};
		}
	}
	Subexp mkrep(const Subexp &lh, NInt m, NInt n, NInt nstk) {
		if ((m != (NInt) -1 && m > RE_DUP_MAX) || (n != (NInt) -1 && n > RE_DUP_MAX) || m > n)
			return {{}, 0, false, MINRX_REG_BADBR};
		if (n == 0)
			return {{}, 0, false, MINRX_REG_SUCCESS};
		if (m == 0 && n == 1)
			return mkrep(lh, true, false, nstk);
		if (m == 0 && n == (NInt) -1)
			return mkrep(lh, true, true, nstk);
		if (m == 1 && n == 1)
			return lh;
		if (m == 1 && n == (NInt) -1)
			return mkrep(lh, false, true, nstk);
		auto [lhs, lhmaxstk, lhasmin, _] = lh;
		auto [rhs, rhmaxstk, rhasmin,__] = lh;
		NInt k;
		for (k = 1; k < m; ++k)
			lhs.insert(lhs.end(), rhs.begin(), rhs.end());
		if (n != (NInt) -1 && k < n) {
			lhmaxstk += 2;
			rhmaxstk += 2;
			for (auto &r : rhs)
				r.nstk += 2;
			auto rhsize = rhs.size();
			rhs.push_front({Node::Skip, {rhsize, 1}, nstk + 2});
			for (; k < n; ++k)
				lhs.insert(lhs.end(), rhs.begin(), rhs.end());
		}
		if (n == (NInt) -1) {
			lhmaxstk += 3;
			rhmaxstk += 3;
			for (auto &r : rhs)
				r.nstk += 3;
			auto rhsize = rhs.size();
			rhs.push_front({Node::Loop, {rhsize, 1}, nstk + 3});
			rhs.push_back({Node::Next, {rhsize, 1}, nstk});
			lhs.insert(lhs.end(), rhs.begin(), rhs.end());
		}
		if (m == 0)
			return mkrep({lhs, rhmaxstk, rhasmin, MINRX_REG_SUCCESS}, true, false, nstk);
		else
			return {lhs, rhmaxstk, rhasmin, MINRX_REG_SUCCESS};
	}
	Subexp rep(bool nested, NInt nstk) {
		auto lh = chr(nested, nstk);
		if (std::get<minrx_result_t>(lh))
			return lh;
		auto hasmin = std::get<bool>(lh);
		for (;;) {
			bool infinite = false, minimal = (flags & MINRX_REG_MINIMAL) != 0, optional = false;
			switch (wc) {
			case L'?':
				optional = true;
				goto common;
			case L'*':
				infinite = optional = true;
				goto common;
			case L'+':
				infinite = true;
			common:	if ((flags & MINRX_REG_MINDISABLE) == 0 && (wc = wconv.nextchr()) == L'?')
					minimal ^= true, wc = wconv.nextchr();
				if (hasmin)
					minraise(lh);
				lh = mkrep(minimal ? minimize(lh, nstk) : lh, optional, infinite, nstk);
			comout:	if (minimal) {
					std::get<0>(lh).push_front({Node::MinB, {0, 0}, nstk});
					hasmin = true;
				}
				std::get<bool>(lh) = hasmin;
				continue;
			case L'{':
				if ((flags & MINRX_REG_BRACE_COMPAT) == 0
				    || (enc == WConv::Encoding::Byte ? std::isdigit(wconv.lookahead())
								     : std::iswdigit(wconv.lookahead())))
				{
					wc = wconv.nextchr();
					if (wc == WConv::End)
						return {{}, 0, false, MINRX_REG_EBRACE};
					NInt m, n;
					if (!num(m, wc))
						return {{}, 0, false, MINRX_REG_BADBR};
					if (wc == L'}') {
						if ((flags & MINRX_REG_MINDISABLE) == 0 && (wc = wconv.nextchr()) == L'?')
							minimal ^= true, wc = wconv.nextchr();
						if (hasmin)
							minraise(lh);
						lh = mkrep(minimal ? minimize(lh, nstk) : lh, m, m, nstk);
						goto comout;
					}
					if (wc == WConv::End)
						return {{}, 0, false, MINRX_REG_EBRACE};
					if (wc != L',')
						return {{}, 0, false, MINRX_REG_BADBR};
					wc = wconv.nextchr();
					if (wc == L'}') {
						if ((flags & MINRX_REG_MINDISABLE) == 0 && (wc = wconv.nextchr()) == L'?')
							minimal ^= true, wc = wconv.nextchr();
						if (hasmin)
							minraise(lh);
						lh = mkrep(minimal ? minimize(lh, nstk) : lh, m, -1, nstk);
						goto comout;
					}
					if (!num(n, wc))
						return {{}, 0, false, MINRX_REG_BADBR};
					if (wc == WConv::End)
						return {{}, 0, false, MINRX_REG_EBRACE};
					if (wc != L'}')
						return {{}, 0, false, MINRX_REG_BADBR};
					if ((flags & MINRX_REG_MINDISABLE) == 0 && (wc = wconv.nextchr()) == L'?')
						minimal ^= true, wc = wconv.nextchr();
					if (hasmin)
						minraise(lh);
					lh = mkrep(minimal ? minimize(lh, nstk) : lh, m, n, nstk);
					goto comout;
				}
				// fall through
			default:
				return lh;
			}
		}
	}
	Subexp chr(bool nested, NInt nstk) {
		std::deque<Node> lhs;
		std::size_t lhmaxstk;
		bool lhasmin = false;
		switch (wc) {
		default:
		normal:
			lhmaxstk = nstk;
			if ((flags & MINRX_REG_ICASE) == 0) {
				lhs.push_back({(NInt) wc, {0, 0}, nstk});
			} else {
				WChar wcl = enc == WConv::Encoding::Byte ? std::tolower(wc) : std::towlower(wc);
				WChar wcu = enc == WConv::Encoding::Byte ? std::toupper(wc) : std::towupper(wc);
				if (wc != wcl || wc != wcu) {
					auto key = std::min(wc, std::min(wcl, wcu));
					if (icmap.find(key) == icmap.end()) {
						icmap.emplace(key, csets.size());
						csets.emplace_back(enc);
						csets.back().set(wc);
						csets.back().set(wcl);
						csets.back().set(wcu);
					}
					lhs.push_back({Node::CSet, {icmap[key], 0}, nstk});
				} else {
					lhs.push_back({(NInt) wc, {0, 0}, nstk});
				}
			}
			wc = wconv.nextchr();
			break;
		case L'{':
			if ((flags & MINRX_REG_BRACE_COMPAT) != 0
			    && (enc == WConv::Encoding::Byte ? !std::isdigit(wconv.lookahead())
							     : !std::iswdigit(wconv.lookahead())))
				goto normal;
			// fall through
		case L'*':
		case L'+':
		case L'?':
			return {{}, 0, false, MINRX_REG_BADRPT};
		case L'[':
			lhmaxstk = nstk;
			lhs.push_back({Node::CSet, {csets.size(), 0}, nstk});
			if (auto err = csets.emplace_back(enc).parse(flags, enc, wconv))
				return {{}, 0, false, err};
			wc = wconv.nextchr();
			break;
		case L'.':
			if (!dot.has_value()) {
				dot = csets.size();
				csets.emplace_back(enc);
				if ((flags & MINRX_REG_NEWLINE) != 0)
					csets.back().set(L'\n');
				csets.back().invert();
			}
			lhmaxstk = nstk;
			lhs.push_back({Node::CSet, {*dot, 0}, nstk});
			wc = wconv.nextchr();
			break;
		case L'^':
			lhmaxstk = nstk;
			lhs.push_back({(flags & MINRX_REG_NEWLINE) == 0 ? Node::ZBOB : Node::ZBOL, {0, 0}, nstk});
			wc = wconv.nextchr();
			break;
		case L'$':
			lhmaxstk = nstk;
			lhs.push_back({(flags & MINRX_REG_NEWLINE) == 0 ? Node::ZEOB : Node::ZEOL, {0, 0}, nstk});
			wc = wconv.nextchr();
			break;
		case L'\\':
			lhmaxstk = nstk;
			wc = wconv.nextchr();
			switch (wc) {
			case L'<':
				if ((flags & MINRX_REG_EXTENSIONS_BSD) == 0)
					goto normal;
				lhs.push_back({Node::ZBOW, {0, 0}, nstk});
				break;
			case L'>':
				if ((flags & MINRX_REG_EXTENSIONS_BSD) == 0)
					goto normal;
				lhs.push_back({Node::ZEOW, {0, 0}, nstk});
				break;
			case L'`':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				lhs.push_back({Node::ZBOB, {0, 0}, nstk});
				break;
			case L'\'':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				lhs.push_back({Node::ZEOB, {0, 0}, nstk});
				break;
			case L'b':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				lhs.push_back({Node::ZXOW, {0, 0}, nstk});
				break;
			case L'B':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				lhs.push_back({Node::ZNWB, {0, 0}, nstk});
				break;
			case L's':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!esc_s.has_value()) {
					esc_s = csets.size();
					WConv wc(enc, "[:space:]]");
					csets.emplace_back(enc).parse(flags, enc, wc);
				}
				lhs.push_back({Node::CSet, {*esc_s, 0}, nstk});
				break;
			case L'S':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!esc_S.has_value()) {
					esc_S = csets.size();
					WConv wc(enc, "^[:space:]]");
					csets.emplace_back(enc).parse(flags, enc, wc);
				}
				lhs.push_back({Node::CSet, {*esc_S, 0}, nstk});
				break;
			case L'w':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!esc_w.has_value()) {
					esc_w = csets.size();
					WConv wc(enc, "[:alnum:]_]");
					csets.emplace_back(enc).parse(flags, enc, wc);
				}
				lhs.push_back({Node::CSet, {*esc_w, 0}, nstk});
				break;
			case L'W':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!esc_W.has_value()) {
					esc_W = csets.size();
					WConv wc(enc, "^[:alnum:]_]");
					csets.emplace_back(enc).parse(flags, enc, wc);
				}
				lhs.push_back({Node::CSet, {*esc_W, 0}, nstk});
				break;
			case WConv::End:
				return {{}, 0, false, MINRX_REG_EESCAPE};
			default:
				goto normal;
			}
			wc = wconv.nextchr();
			break;
		case L'(':
			{
				NInt n = ++nsub;
				wc = wconv.nextchr();
				minrx_result_t err;
				std::tie(lhs, lhmaxstk, lhasmin, err) = alt(true, nstk + 1);
				if (err)
					return {lhs, lhmaxstk, lhasmin, err};
				if (wc != L')')
					return {{}, 0, false, MINRX_REG_EPAREN};
				lhs.push_front({Node::SubL, {n, nsub}, nstk + 1});
				lhs.push_back({Node::SubR, {n, nsub}, nstk});
				wc = wconv.nextchr();
			}
			break;
		case L')':
			if (!nested)
				goto normal;
			// fall through
		case L'|':
		case WConv::End:
			lhmaxstk = nstk;
			break;
		}
		return {lhs, lhmaxstk, lhasmin, MINRX_REG_SUCCESS};
	}
	std::optional<CSet> firstclosure(const std::vector<Node> &nodes) {
		if (nodes.size() == 0)
			return {};
		QSet<NInt> epsq(nodes.size()), epsv(nodes.size()), firsts(nodes.size());
		auto add = [&epsq, &epsv](NInt n) { if (!epsv.contains(n)) { epsq.insert(n); epsv.insert(n); } };
		epsq.insert(0);
		do {
			auto k = epsq.remove();
			auto &n = nodes[k];
			if (n.type <= Node::CSet)
				firsts.insert(k);
			else
				switch (n.type) {
				case Node::Exit:
					return {};
				case Node::Fork:
					do {
						add(k + 1);
						k = k + 1 + nodes[k].args[0];
					} while (nodes[k].type != Node::Join);
					break;
				case Node::Goto:
					add(k + 1 + n.args[0]);
					break;
				case Node::Loop:
					add(k + 1);
					if (n.args[1])
						add(k + 1 + n.args[0]);
					break;
				case Node::Skip:
					add(k + 1);
					add(k + 1 + n.args[0]);
					break;
				default:
					add(k + 1);
					break;
				}
		} while (!epsq.empty());
		CSet cs(enc);
		while (!firsts.empty()) {
			auto k = firsts.remove();
			auto t = nodes[k].type;
			if (t <= WCharMax)
				cs.set(t);
			else
				cs |= csets[nodes[k].args[0]];
		}
		return cs;
	}
	std::pair<std::optional<const std::array<bool, 256>>, std::optional<char>>
	firstbytes(WConv::Encoding e, const std::optional<CSet>& firstcset) {
		if (!firstcset.has_value())
			return {};
		return firstcset->firstbytes(e);
	}
	Regexp *compile() {
		if ((flags & MINRX_REG_MINDISABLE) != 0 && (flags & MINRX_REG_MINIMAL) != 0)
			return new Regexp { enc, MINRX_REG_BADPAT, {}, {}, {}, {}, {}, 0, 0, 1 };
		auto [lhs, nstk, hasmin, err] = alt(false, 0);
		if (err) {
			csets.clear();
			lhs.clear();
			nmin = 0;
			nstk = 0;
			nsub = 0;
		} else {
			lhs.push_back({Node::Exit, {0, 0}, 0});
		}
		if (nmin > 0)
			for (auto &l : lhs) l.nstk += nmin;
		std::vector<Node> nodes{lhs.begin(), lhs.end()};
		auto fc = firstclosure(nodes);
		auto [fb, fu] = firstbytes(enc, fc);
		return new Regexp{ enc, err, std::move(csets), std::move(nodes), std::move(fc), std::move(fb), std::move(fu), nmin, nstk, nsub + 1 };
	}
};

struct Execute {
	constexpr static std::size_t SizeBits = std::numeric_limits<std::size_t>::digits;
	typedef COWVec<std::size_t, (std::size_t) -1> Vec;
	struct NState {
		std::size_t gen = 0;
		std::size_t boff;
		Vec substack;
		NState() {}
		NState(Vec::Allocator &allocator): substack(allocator) {}
		template <typename... XArgs>
		auto cmp(const NState &ns, std::size_t gen, std::size_t nstk, XArgs... xargs) const {
			if (gen != ns.gen)
				return gen <=> ns.gen;
			if (boff != ns.boff)
				return ns.boff <=> boff;
			if (auto x = substack.cmp(ns.substack, nstk, xargs...); x != 0)
				return x;
			return 0 <=> 0;
		}
	};
	const Regexp &r;
	const minrx_regexec_flags_t flags;
	const std::size_t suboff = r.nmin + r.nstk;
	const std::size_t minvcnt = (r.nmin + SizeBits - 1) / SizeBits;
	const std::size_t minvoff = suboff + 2 * r.nsub;
	const std::size_t nestoff = minvoff + minvcnt;
	std::size_t gen = 0;
	std::size_t off = 0;
	WConv wconv;
	WChar wcprev = WConv::End;
	Vec::Allocator allocator { nestoff + r.nmin };
	std::optional<Vec> best;
	NInt bestmincount = 0; // note mincounts are negated so this means +infinity
	QSet<NInt> epsq { r.nodes.size() };
	QVec<NInt, NState> epsv { r.nodes.size() };
	const Node *nodes = r.nodes.data();
	Execute(const Regexp &r, minrx_regexec_flags_t flags, const char *bp, const char *ep) : r(r), flags(flags), wconv(r.enc, bp, ep) {}
	template <typename... XArgs>
	INLINE
	void add(QVec<NInt, NState> &ncsv, NInt k, NInt nstk, const NState &ns, WChar wcnext, XArgs... xargs) {
		const Node &n = nodes[k];
		if (n.type <= Node::CSet) {
			if (n.type == (NInt) wcnext || (n.type == Node::CSet && r.csets[n.args[0]].test(wcnext))) {
				auto [newly, newns] = ncsv.insert(k, ns);
				if (newly)
					new (&newns) NState(ns);
				else if (auto x = ns.cmp(newns, gen, nstk, xargs...); x > 0 || (x == 0 && minvcnt && ns.substack.cmp(minvoff, minvcnt, newns.substack) > 0))
					newns = ns;
				else
					return;
				newns.gen = gen;
				if constexpr (sizeof... (XArgs) > 0) {
					auto i = nstk - sizeof...(XArgs);
					(newns.substack.put(i++, xargs), ...);
				}
			}
		} else {
			auto [newly, newns] = epsv.insert(k, ns);
			if (newly)
				new (&newns) NState(ns);
			else if (auto x = ns.cmp(newns, gen, nstk, xargs...); x > 0 || (x == 0 && minvcnt && ns.substack.cmp(minvoff, minvcnt, newns.substack) > 0))
				newns = ns;
			else
				return;
			newns.gen = gen;
			if constexpr (sizeof... (XArgs) > 0) {
				auto i = nstk - sizeof...(XArgs);
				(newns.substack.put(i++, xargs), ...);
			}
			epsq.insert(k);
		}
	}
	void epsclosure(QVec<NInt, NState> &ncsv, WChar wcnext) {
		auto nodes = this->nodes;
		auto is_word = r.enc == WConv::Encoding::Byte ? [](WChar b) { return b == '_' || std::isalnum(b); }
							      : [](WChar wc) { return wc == L'_' || std::iswalnum(wc); };
		do {
			NInt k = epsq.remove();
			NState &ns = epsv.lookup(k);
			if (best.has_value() && ns.boff > best->get(suboff + 0))
				continue;
			const auto &n = nodes[k];
			auto nstk = n.nstk;
			switch (n.type) {
			case Node::Exit:
				{
					auto b = ns.boff, e = off, mincount = r.nmin ? ns.substack.get(0) : (NInt) -1;
					bool minvalid = r.nmin ? ns.substack.get(minvoff) < ((std::size_t) 1 << (SizeBits - 1)) : false;
					if (!best.has_value()
					    || b < best->get(suboff + 0)
					    || (b == best->get(suboff + 0) && e > best->get(suboff + 1) && (!minvalid || mincount >= bestmincount)))
					{
						best = ns.substack;
						best->put(suboff + 0, b);
						best->put(suboff + 1, e);
						if (minvalid)
							bestmincount = std::max(bestmincount, mincount);
					}
				}
				break;
			case Node::Fork:
				{
					NInt priority = (NInt) -1;
					do {
						add(ncsv, k + 1, nstk, ns, wcnext, priority--);
						k = k + 1 + nodes[k].args[0];
					} while (nodes[k].type != Node::Join);
				}
				break;
			case Node::Goto:
				add(ncsv, k + 1 + n.args[1], nstk, ns, wcnext);
				break;
			case Node::Join:
				add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			case Node::Loop:
				add(ncsv, k + 1, nstk, ns, wcnext, (NInt) off, (NInt) -1, (NInt) off);
				if (n.args[1])
					add(ncsv, k + 1 + n.args[0], nstk, ns, wcnext, (NInt) off, (NInt) 0, (NInt) off);
				break;
			case Node::MinB:
				{
					std::size_t w = n.args[0] / SizeBits;
					std::size_t b = (std::size_t) 1 << (SizeBits - 1 - n.args[0] % SizeBits);
					NState nscopy = ns;
					b |= -b;
					auto x = nscopy.substack.get(minvoff + w);
					do {
						if ((x & b) != 0)
							nscopy.substack.put(minvoff + w, x & ~b);
						b = -1;
					} while ( w-- > 0);
					add(ncsv, k + 1, nstk, nscopy, wcnext);
				}
				break;
			case Node::MinL:
				add(ncsv, k + 1, nstk, ns, wcnext, off);
				break;
			case Node::MinR:
				{
					NState nscopy = ns;
					auto mininc = off - nscopy.substack.get(n.nstk);
					std::size_t oldlen = (std::size_t) -1 - nscopy.substack.get(n.args[0]);
					mininc -= nscopy.substack.get(nestoff + n.args[0]);
					nscopy.substack.put(nestoff + n.args[0], 0);
					nscopy.substack.put(n.args[0], (std::size_t) -1 - (oldlen + mininc));
					for (auto i = n.args[0]; i-- > 0; ) {
						oldlen = (std::size_t) -1 - nscopy.substack.get(i);
						nscopy.substack.put(i, -1 - (oldlen + mininc));
						nscopy.substack.put(nestoff + i, nscopy.substack.get(nestoff + i) + mininc);
					}
					add(ncsv, k + 1, nstk, nscopy, wcnext);
				}
				break;
			case Node::Next:
				add(ncsv, k + 1, nstk, ns, wcnext);
				if (n.args[1] && off > ns.substack.get(nstk + 3 - 1))
					add(ncsv, k - n.args[0], nstk + 3, ns, wcnext, ns.substack.get(nstk), ns.substack.get(nstk + 1) - 1, (NInt) off);
				break;
			case Node::Skip:
				add(ncsv, k + 1, nstk, ns, wcnext, (NInt) off, (NInt) 1 ^ n.args[1]);
				add(ncsv, k + 1 + n.args[0], nstk, ns, wcnext, (NInt) off, (NInt) 0 ^ n.args[1]);
				break;
			case Node::SubL:
				{
					NState nscopy = ns;
					nscopy.substack.put(nstk - 1, off);
					if (n.args[0] != (NInt) -1 && (flags & MINRX_REG_NOSUBRESET) == 0)
						for (auto i = n.args[0] + 1; i <= n.args[1]; ++i) {
							nscopy.substack.put(suboff + i * 2, -1);
							nscopy.substack.put(suboff + i * 2 + 1, -1);
						}
					add(ncsv, k + 1, nstk, nscopy, wcnext);
				}
				break;
			case Node::SubR:
				if (n.args[0] != (NInt) -1 && ((flags & MINRX_REG_FIRSTSUB) == 0 || ns.substack.get(suboff + n.args[0] * 2) == (NInt) -1)) {
					NState nscopy = ns;
					nscopy.substack.put(suboff + n.args[0] * 2 + 0, ns.substack.get(nstk));
					nscopy.substack.put(suboff + n.args[0] * 2 + 1, off);
					add(ncsv, k + 1, nstk, nscopy, wcnext);
				} else {
					add(ncsv, k + 1, nstk, ns, wcnext);
				}
				break;
			case Node::ZBOB:
				if (off == 0 && (flags & MINRX_REG_NOTBOL) == 0)
					add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			case Node::ZEOB:
				if (wcnext == WConv::End && (flags & MINRX_REG_NOTEOL) == 0)
					add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			case Node::ZBOL:
				if (((off == 0 && (flags & MINRX_REG_NOTBOL) == 0)) || wcprev == L'\n')
					add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			case Node::ZEOL:
				if (((wcnext == WConv::End && (flags & MINRX_REG_NOTEOL) == 0)) || wcnext == L'\n')
					add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			case Node::ZBOW:
				if ((off == 0 || !is_word(wcprev)) && (wcnext != WConv::End && is_word(wcnext)))
					add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			case Node::ZEOW:
				if ((off != 0 && is_word(wcprev)) && (wcnext == WConv::End || !is_word(wcnext)))
					add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			case Node::ZXOW:
				if (   ((off == 0 || !is_word(wcprev)) && (wcnext != WConv::End && is_word(wcnext)))
				    || ((off != 0 && is_word(wcprev)) && (wcnext == WConv::End || !is_word(wcnext))))
					add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			case Node::ZNWB:
				if (   (off == 0 && wcnext == WConv::End)
				    || (off == 0 && wcnext != WConv::End && !is_word(wcnext))
				    || (off != 0 && !is_word(wcprev) && wcnext == WConv::End)
				    || (off != 0 && wcnext != WConv::End && is_word(wcprev) == is_word(wcnext)))
					add(ncsv, k + 1, nstk, ns, wcnext);
				break;
			default:
				abort();
				break;
			}
		} while (!epsq.empty());
	}
	int execute(std::size_t nm, minrx_regmatch_t *rm) {
		QVec<NInt, NState> mcsvs[2] { r.nodes.size(), r.nodes.size() };
		off = wconv.off();
		auto wcnext = wconv.nextchr();
		if ((flags & MINRX_REG_RESUME) != 0 && rm && rm[0].rm_eo > 0)
			while (wcnext != WConv::End && (std::ptrdiff_t) off < rm[0].rm_eo)
				wcprev = wcnext, off = wconv.off(), wcnext = wconv.nextchr();
		NState nsinit(allocator);
		if ((flags & MINRX_REG_NOFIRSTBYTES) == 0 && r.firstbytes.has_value() && !r.firstcset->test(wcnext)) {
		zoom:
			auto cp = wconv.cp, ep = wconv.ep;
			if (r.firstunique.has_value()) {
				cp = (const char *) std::memchr(cp, *r.firstunique, ep - cp);
				if (cp == nullptr)
					goto exit;
			} else {
				auto firstbytes = *r.firstbytes;
				while (cp != ep && !firstbytes[(unsigned char) *cp])
					++cp;
				if (cp == ep)
					goto exit;
			}
			if (cp != wconv.cp) {
				if (r.enc == WConv::Encoding::UTF8) {
					auto bp = cp;
					while (bp != wconv.cp && cp - bp < 8 && (unsigned char) *--bp >= 0x80)
						;
					wconv.cp = (unsigned char) *bp >= 0x80 ? cp - 1 : bp;
				} else {
					wconv.cp = cp - 1;
				}
				wcnext = wconv.nextchr();
			}
			++gen, wcprev = wcnext, off = wconv.off(), wcnext = wconv.nextchr();
		}
		nsinit.boff = off;
		for (std::size_t i = 0; i < r.nmin; ++i)
			nsinit.substack.put(nestoff + i, 0);
		add(mcsvs[0], 0, 0, nsinit, wcnext);
		if (!epsq.empty())
			epsclosure(mcsvs[0], wcnext);
		for (;;) { // unrolled to ping-pong roles of mcsvs[0]/[1]
			if (wcnext == WConv::End)
				break;
			++gen;
			wcprev = wcnext, off = wconv.off(), wcnext = wconv.nextchr();
			while (!mcsvs[0].empty()) {
				auto [n, ns] = mcsvs[0].remove();
				add(mcsvs[1], n + 1, nodes[n].nstk, ns, wcnext);
			}
			if (!best.has_value()) {
				nsinit.boff = off;
				add(mcsvs[1], 0, 0, nsinit, wcnext);
			}
			if (!epsq.empty())
				epsclosure(mcsvs[1], wcnext);
			if (mcsvs[1].empty()) {
				if (best.has_value())
					break;
				if ((flags & MINRX_REG_NOFIRSTBYTES) == 0 && r.firstbytes.has_value())
					goto zoom;
			}
			if (wcnext == WConv::End)
				break;
			++gen;
			wcprev = wcnext, off = wconv.off(), wcnext = wconv.nextchr();
			while (!mcsvs[1].empty()) {
				auto [n, ns] = mcsvs[1].remove();
				add(mcsvs[0], n + 1, nodes[n].nstk, ns, wcnext);
			}
			if (!best.has_value()) {
				nsinit.boff = off;
				add(mcsvs[0], 0, 0, nsinit, wcnext);
			}
			if (!epsq.empty())
				epsclosure(mcsvs[0], wcnext);
			if (mcsvs[0].empty()) {
				if (best.has_value())
					break;
				if ((flags & MINRX_REG_NOFIRSTBYTES) == 0 && r.firstbytes.has_value())
					goto zoom;
			}
		}
	exit:
		if (best.has_value()) {
			if (rm) {
				std::size_t nsub = std::min(nm, r.nsub);
				std::size_t i;
				for (i = 0; i < nsub; ++i) {
					rm[i].rm_so = (*best->storage)[suboff + i * 2];
					rm[i].rm_eo = (*best->storage)[suboff + i * 2 + 1];
				}
				for (; i < nm; ++i)
					rm[i].rm_so = rm[i].rm_eo = -1;
			}
			return 0;
		} else {
			if (rm)
				for (std::size_t i = 0; i < nm; ++i)
					rm[i].rm_so = rm[i].rm_eo = -1;
			return MINRX_REG_NOMATCH;
		}
	}
};

}

int
minrx_regcomp(minrx_regex_t *rx, const char *s, int flags)
{
	return minrx_regncomp(rx, strlen(s), s, flags);
}

int
minrx_regexec(minrx_regex_t *rx, const char *s, std::size_t nm, minrx_regmatch_t *rm, int flags)
{
	return minrx_regnexec(rx, strlen(s), s, nm, rm, flags);
}

int
minrx_regncomp(minrx_regex_t *rx, std::size_t ns, const char *s, int flags)
{
	auto enc = Encoding_MBtoWC;
	auto loc = setlocale(LC_CTYPE, nullptr);
	if ((strcmp(loc, "C") == 0 || (flags & MINRX_REG_NATIVE1B) != 0) && MB_CUR_MAX == 1)
		enc = Encoding_Byte;
	else if (strcmp(nl_langinfo(CODESET), "UTF-8") == 0)
		enc = Encoding_UTF8;
	auto r = MinRX::Compile(enc, s, s + ns, (minrx_regcomp_flags_t) flags).compile();
	rx->re_regexp = r;
	rx->re_nsub = r->nsub - 1;
	rx->re_compflags = (minrx_regcomp_flags_t) flags;
	return r->err;
}

int
minrx_regnexec(minrx_regex_t *rx, std::size_t ns, const char *s, std::size_t nm, minrx_regmatch_t *rm, int flags)
{
	MinRX::Regexp *r = reinterpret_cast<MinRX::Regexp *>(rx->re_regexp);
	return MinRX::Execute(*r, (minrx_regexec_flags_t) flags, s, s + ns).execute(nm, rm);
}

void
minrx_regfree(minrx_regex_t *rx)
{
	delete reinterpret_cast<MinRX::Regexp *>(rx->re_regexp);
	rx->re_regexp = nullptr;
}

size_t
minrx_regerror(int errcode, const minrx_regex_t *, char *errbuf, size_t errsize)
{
	static const char *const messages[] = {
		N_("success"),
		N_("bad pattern"),
		N_("invalid contents of {}"),
		N_("? * + or {interval} not preceded by valid subpattern"),
		N_("unbalanced {"),
		N_("unbalanced ["),
		N_("invalid collating element"),
		N_("invalid character class name"),
		N_("invalid trailing backslash"),
		N_("unbalanced ("),
		N_("invalid range endpoint"),
		N_("memory allocation failed"),
		N_("invalid \\digit"),
		N_("match not found"),
		N_("unknown error code"),
	};
	if (errcode < 0 || errcode > MINRX_REG_UNKNOWN)
		errcode = MINRX_REG_UNKNOWN;
	size_t size = snprintf(errbuf, errsize, "%s", _(messages[errcode]));
	if (errsize != 0 && size == errsize)
		errbuf[errsize - 1] = '\0';
	return size + 1;
}
#endif
