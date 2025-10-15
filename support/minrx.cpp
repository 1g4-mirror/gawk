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
//

// ISO C
#include <ctype.h>
#include <limits.h>
#include <locale.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <wchar.h>
#include <wctype.h>

// ISO C++
#include <array>
#include <limits>
#include <map>
#include <mutex>
#include <optional>
#include <set>
#include <string>
#include <tuple>
#include <vector>

// POSIX
#include <langinfo.h>

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif /* HAVE_CONFIG_H */

// GNU gettext
#ifdef HAVE_GETTEXT_H
#include <gettext.h>
#define _(msgid)  gettext(msgid)
#else /* ! HAVE_GETTEXT_H */
#define _(msgid)  msgid
#endif /* ! HAVE_GETTEXT_H */
#define N_(msgid) msgid

// Arnold Robbins' charset library
#ifdef CHARSET
#include <memory>
#include "charset.h"
#endif

#include "minrx.h"

#ifdef __GNUC__
#define inline __attribute__((__always_inline__)) inline
#endif

static inline
bool IsDigit(int32_t wc)
{
	return wc >= L'0' && wc <= L'9';
}

#ifdef __GNUC__
// FIXME: expand compiler support beyond clang and gcc
#if UINT_MAX == 18446744073709551615U
#define ctz __builtin_ctz
#elif ULONG_MAX == 18446744073709551615U
#define ctz __builtin_ctzl
#elif ULLONG_MAX == 18446744073709551615U
#define ctz __builtin_ctzll
#else
#error "can't figure out how to count trailing zeroes for 64-bit operands"
#endif
#else
// ctz --- count trailing zeros. dead simple table driven version

int
ctz(uint64_t val)
{
	static char table[] = {
		8, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		7, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		6, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		5, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
		4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0,
	};

	if (val == 0)
		return 64;

	int count = 0;
	for (; val != 0; val >>= 8) {
		uint32_t x = val & 0xFF;

		if (x == 0) {
			count += 8;
			continue;
		}
		
		count += table[x];
		break;
	}

	return count;
}
#endif

#define MAX(A, B) ((A) >= (B) ? (A) : (B))
#define MIN(A, B) ((A) <= (B) ? (A) : (B))

namespace MinRX {

typedef struct COWVec_Allocator COWVec_Allocator;
typedef struct COWVec_Storage COWVec_Storage;
typedef struct COWVec COWVec;

struct COWVec_Allocator {
	size_t length;
	COWVec_Storage *freelist = nullptr;
};

struct COWVec_Storage {
	union {
		COWVec_Allocator *allocator;
		COWVec_Storage *freelink;
	} u;
	size_t refcnt;
	size_t hack[1];
};

struct COWVec {
	COWVec_Storage *storage;
};

static void
cowvec_allocator_construct(COWVec_Allocator *a, size_t length)
{
	a->length = length;
	a->freelist = nullptr;
}

static void
cowvec_allocator_destruct(COWVec_Allocator *a)
{
	for (COWVec_Storage *s = a->freelist, *sfreelink = nullptr; s != nullptr; s = sfreelink) {
		sfreelink = s->u.freelink;
		free(s);
	}
}

static size_t
cowvec_storage_get(const COWVec_Storage *cvs, size_t i)
{
	return (&cvs->hack[0])[i];
}

static const size_t *
cowvec_storage_getref(const COWVec_Storage *cvs, size_t i)
{
	return &(&cvs->hack[0])[i];
}

static void
cowvec_storage_put(COWVec_Storage *cvs, size_t i, size_t v)
{
	(&cvs->hack[0])[i] = v;
}

static COWVec_Storage *
cowvec_storage_alloc(COWVec_Allocator *a)
{
	COWVec_Storage *r;
	if (a->freelist) {
		r = a->freelist;
		a->freelist = r->u.freelink;
		r->u.allocator = a;
		r->refcnt = 1;
	} else {
		r = (COWVec_Storage *) malloc(sizeof (COWVec_Storage) + (a->length - 1) * sizeof (size_t));
		r->u.allocator = a;
		r->refcnt = 1;
	}
	for (size_t i = 0, n = a->length; i != n; ++i)
		cowvec_storage_put(r, i, -1);
	return r;
}

static COWVec_Storage *
cowvec_storage_clone(COWVec_Storage *cvs)
{
	COWVec_Storage *newcvs = cowvec_storage_alloc(cvs->u.allocator);
	for (size_t i = 0, n = cvs->u.allocator->length; i != n; ++i)
		cowvec_storage_put(newcvs, i, cowvec_storage_get(cvs, i));
	return newcvs;
}

static void
cowvec_storage_dealloc(COWVec_Allocator *a, COWVec_Storage *s)
{
	s->u.freelink = a->freelist;
	a->freelist = s;
}

static void
cowvec_construct(COWVec *c, COWVec_Allocator *a)
{
	c->storage = a ? cowvec_storage_alloc(a) : nullptr;
}

static void
cowvec_destruct(COWVec *c)
{
	if (c->storage && --c->storage->refcnt == 0)
		cowvec_storage_dealloc(c->storage->u.allocator, c->storage);
	c->storage = nullptr;
}

static size_t
cowvec_get(COWVec *cv, size_t idx)
{
	return cowvec_storage_get(cv->storage, idx);
}

static void
cowvec_put(COWVec *cv, size_t idx, size_t val)
{
	if (cowvec_storage_get(cv->storage, idx) == val)
		return;
	if (cv->storage->refcnt > 1) {
		--cv->storage->refcnt;
		cv->storage = cowvec_storage_clone(cv->storage);
		cv->storage->refcnt = 1;
	}
	cowvec_storage_put(cv->storage, idx, val);
}

static void
cowvec_copy(COWVec *dst, const COWVec *src)
{
	++src->storage->refcnt;
	if (dst->storage && --dst->storage->refcnt == 0)
		cowvec_storage_dealloc(dst->storage->u.allocator, dst->storage);
	dst->storage = src->storage;
}

static void
cowvec_move(COWVec *dst, COWVec *src)
{
	if (dst->storage && --dst->storage->refcnt == 0)
		cowvec_storage_dealloc(dst->storage->u.allocator, dst->storage);
	dst->storage = src->storage;
	src->storage = nullptr;
}

template <typename... XArgs>
static auto
cowvec_cmp(const COWVec *xcv, const COWVec *ycv, size_t limit, XArgs... xargs)
{
	size_t i;
	const size_t *xv = cowvec_storage_getref(xcv->storage, 0);
	const size_t *yv = cowvec_storage_getref(ycv->storage, 0);
	for (i = 0; i < limit - sizeof... (XArgs); i++)
		if (xv[i] != yv[i])
			return xv[i] <=> yv[i];
	if constexpr (sizeof...(XArgs) > 0)
		for (size_t x : { xargs... })
			if (x != yv[i++])
				return x <=> yv[i - 1];
	return (size_t) 0 <=> (size_t) 0;
}

static auto
cowvec_cmp_from(size_t o, const COWVec *xcv, const COWVec *ycv, size_t n)
{
	const size_t *xv = cowvec_storage_getref(xcv->storage, 0);
	const size_t *yv = cowvec_storage_getref(ycv->storage, 0);
	for (size_t i = 0; i < n; i++)
		if (xv[o + i] != yv[o + i])
			return xv[o + i] <=> yv[o + i];
	return (size_t) 0 <=> (size_t) 0;
}

static bool
cowvec_valid(const COWVec *c)
{
	return c->storage != nullptr;
}

struct QSet {
	uint64_t *bits[10];
	uint64_t bits0;
	uint64_t *bitsfree;
	int depth;
};

static bool
qset_construct(QSet *q, size_t limit)
{
	size_t s[10], t = 0;
	q->depth = 0;
	do
		t += (limit = s[q->depth++] = (limit + 63u) / 64u);
	while (limit > 1);
	uint64_t *next = q->bitsfree = (uint64_t *) malloc(t * sizeof (uint64_t));
	if (!next)
		return false;
	q->bits[0] = &q->bits0;
	for (int i = 1; i < q->depth; ++i)
		q->bits[i] = next, next += s[q->depth - 1 - i];
	q->bits0 = 0;
	return true;
}

static void
qset_destruct(QSet *q)
{
	if (q->bitsfree)
		free(q->bitsfree);
}

static uint64_t
bit(size_t k)
{
	return (uint64_t) 1 << (k & 0x3F);
}

static bool
qset_empty(const QSet *q)
{
	return q->bits0 == 0;
}

static bool
qset_contains(const QSet *q, size_t k)
{
	int i = 0, s = 6 * q->depth;
	size_t j = 0;
	while (i < q->depth) {
		int64_t x = q->bits[i++][j];
		s -= 6;
		j = k >> s;
		int64_t w = bit(j);
		if (!(x & w))
			return false;
	}
	return true;
}

static bool
qset_insert(QSet *q, size_t k)
{
	bool r = false;
	int i = 0, s = 6 * q->depth;
	size_t j = 0;
	while (i < q->depth) {
		uint64_t *bp = &q->bits[i++][j];
		uint64_t x = *bp;
		s -= 6;
		j = k >> s;
		uint64_t w = bit(j);
		if ((x & w) == 0) {
			if (i < q->depth)
				q->bits[i][j] = 0;
			else
				r = true;
		}
		*bp = x | w;
	}
	return r;
}

static size_t
qset_remove(QSet *q) // caller must ensure !empty()
{
	size_t k = 0;
	int i = 0, d = q->depth;
	do
		k = (k << 6) | ctz(q->bits[i++][k]);
	while (i != d);
	size_t r = k;
	do {
		--i;
		uint64_t w = bit(k);
		k >>= 6;
		if ((q->bits[i][k] &= ~w) != 0)
			break;
	} while (i != 0);
	return r;
}

struct NState {
	size_t gen;
	size_t boff;
	COWVec substack;
};

static void
nstate_copy(NState *dstns, const NState *srcns)
{
	dstns->gen = srcns->gen;
	dstns->boff = srcns->boff;
	cowvec_copy(&dstns->substack, &srcns->substack);
}

static void
nstate_move(NState *dstns, NState *srcns)
{
	dstns->gen = srcns->gen;
	dstns->boff = srcns->boff;
	cowvec_move(&dstns->substack, &srcns->substack);
}

static void
nstate_construct(NState *ns, COWVec_Allocator *a)
{
	ns->gen = 0;
	ns->boff = 0;
	cowvec_construct(&ns->substack, a);
}

static void
nstate_destruct(NState *ns)
{
	cowvec_destruct(&ns->substack);
}

static void
nstate_construct_copy(NState *dstns, const NState *srcns)
{
	nstate_construct(dstns, nullptr);
	nstate_copy(dstns, srcns);
}

static void
nstate_construct_move(NState *dstns, NState *srcns)
{
	nstate_construct(dstns, nullptr);
	nstate_move(dstns, srcns);
}

template <typename... XArgs>
static auto
nstate_cmp(const NState *xns, const NState *yns, size_t gen, size_t nstk, XArgs... xargs)
{
	if (gen != yns->gen)
		return gen <=> yns->gen;
	if (xns->boff != yns->boff)
		return yns->boff <=> xns->boff;
	if (auto x = cowvec_cmp(&xns->substack, &yns->substack, nstk, xargs...); x != 0)
		return x;
	return 0 <=> 0;
}

struct QVec {
	QSet qset;
	NState *storage;
};

static void
qvec_construct(QVec *q, size_t l)
{
	if (!qset_construct(&q->qset, l))
		throw std::bad_alloc();
	q->storage = nullptr;
	q->storage = static_cast<NState *>(::operator new(l * sizeof (NState)));
}

static void
qvec_clear(QVec *q)
{
	while (!qset_empty(&q->qset)) {
		size_t i = qset_remove(&q->qset);
		nstate_destruct(&q->storage[i]);
	}
}

static void
qvec_destruct(QVec *q)
{
	qvec_clear(q);
	::operator delete(q->storage);
	qset_destruct(&q->qset);
}

static bool
qvec_empty(QVec *q)
{
	return qset_empty(&q->qset);
}

static std::pair<bool, NState *>
qvec_insert(QVec *q, size_t k, const NState *)
{
	bool newly = qset_insert(&q->qset, k);
	// WARNING: if newly inserted then we are returning a reference to uninitialized memory
	// and it is the caller's responsibility to construct a valid NState there.
	return {newly, &q->storage[k]};
}

static NState *
qvec_lookup(QVec *q, size_t k)
{
	return &q->storage[k];
}

static std::pair<size_t, NState>
qvec_remove(QVec *q)
{
	size_t k = qset_remove(&q->qset);
	std::pair<size_t, NState> r {k, {}};
	nstate_construct_move(&r.second, &q->storage[k]);
	return r;
}

typedef int32_t WChar;			// because wchar_t may not be 32 bits
constexpr int32_t WCharMax = 0x10FFFF;	// maximum code point: valid for Unicode and (FIXME!) blithely assumed for non-Unicode
enum WConv_Encoding { Byte, MBtoWC, UTF8 };
enum { End = -1 };

typedef struct WConv WConv;
struct WConv {
	WChar (*nextfn)(WConv *);
	const char *bp;
	const char *ep;
	const char *cp;
	mbstate_t mbs;
};

static WChar
wconv_nextbyte(WConv *wc)
{
	return wc->cp != wc->ep ? (unsigned char) *wc->cp++ : (WChar) End;
}

static WChar
wconv_nextmbtowc(WConv *wc)
{
	wchar_t wct = L'\0';
	if (wc->cp != wc->ep) {
		size_t n = mbrtowc(&wct, wc->cp, wc->ep - wc->cp, &wc->mbs);
		if (n == 0 || n == (size_t) -1 || n == (size_t) -2) {
			if (wct == L'\0')
				wct = std::numeric_limits<WChar>::min() + (unsigned char) *wc->cp++;
		} else {
			wc->cp += n;
		}
		return wct;
	} else {
		return End;
	}
}

static WChar
wconv_nextutf8(WConv *wc)
{
	if (wc->cp != wc->ep) {
		WChar u = (unsigned char) wc->cp[0];
		if (u < 0x80)
			return wc->cp += 1, u;
		if ((u & 0x40) == 0 || wc->cp + 1 == wc->ep)
		error:
			return wc->cp += 1, std::numeric_limits<WChar>::min() + u;
		WChar v = (unsigned char) wc->cp[1];
		if ((v & 0xC0) != 0x80)
			goto error;
		if ((u & 0x20) == 0) {
			WChar r = ((u & 0x1F) << 6) | (v & 0x3F);
			if (r < 0x80)
				goto error;
			return wc->cp += 2, r;
		}
		if (wc->cp + 2 == wc->ep)
			goto error;
		WChar w = (unsigned char) wc->cp[2];
		if ((w & 0xC0) != 0x80)
			goto error;
		if ((u & 0x10) == 0) {
			WChar r = ((u & 0x0F) << 12) | ((v & 0x3F) << 6) | (w & 0x3F);
			if (r < 0x800)
				goto error;
			return wc->cp += 3, r;
		}
		if (wc->cp + 3 == wc->ep)
			goto error;
		WChar x = (unsigned char) wc->cp[3];
		if ((x & 0xC0) != 0x80)
			goto error;
		if ((u & 0x08) != 0)
			goto error;
		WChar r = ((u & 0x07) << 18) | ((v & 0x3F) << 12) | ((w & 0x3F) << 6) | (x & 0x3F);
		if (r < 0x010000 || r > 0x10FFFF)
			goto error;
		return wc->cp += 4, r;
	} else {
		return End;
	}
}

static WChar (*const wconv_nextfns[3])(WConv *) = { &wconv_nextbyte, &wconv_nextmbtowc, &wconv_nextutf8 };

static void
wconv_construct(WConv *wc, WConv_Encoding e, const char *bp, const char *ep)
{
	wc->nextfn = wconv_nextfns[(int) e];
	wc->bp = bp;
	wc->ep = ep;
	wc->cp = bp;
	memset(&wc->mbs, 0, sizeof wc->mbs);
}

static void
wconv_constructz(WConv *wc, WConv_Encoding e, const char *bp)
{
	wconv_construct(wc, e, bp, bp + strlen(bp));
}

static WChar
wconv_nextchr(WConv *wc)
{
	return wc->nextfn(wc);
}

static WChar
wconv_lookahead(WConv *wc)
{
	WConv wconv = *wc;
	return wconv_nextchr(&wconv);
}

static size_t
wconv_off(const WConv *wc)
{
	return wc->cp - wc->bp;
}

static const char *
wconv_ptr(const WConv *wc)
{
	return wc->cp;
}

static const char *
wconv_save(const WConv *wc)
{
	return wc->cp;
}

static void
wconv_restore(WConv *wc, const char *p)
{
	wc->cp = p;
}

struct CSet {
#ifdef CHARSET
	charset_t *charset = nullptr;
	CSet(WConv_Encoding enc) {
		int errcode = 0;
		charset = charset_create(& errcode, MB_CUR_MAX, enc == UTF8);
		// FIXME: Throw error if charset == nullptr
	}
	CSet(const CSet &) = delete;
	CSet &operator=(const CSet &) = delete;
	CSet(CSet &&cs): charset(cs.charset) { cs.charset = nullptr; }
	CSet &operator=(CSet &&cs) { charset = cs.charset; cs.charset = nullptr; return *this; }
	CSet &operator|=(const CSet &cs) {
		charset_merge(charset, cs.charset);
		return *this;
	}
	~CSet() { if (charset) { charset_free(charset); charset = nullptr; } }
#else
	static std::map<std::string, CSet> cclmemo;
	static std::mutex cclmutex;
	struct Range {
		Range(WChar x, WChar y): min(MIN(x, y)), max(MAX(x, y)) {}
		WChar min, max;
		int operator<=>(const Range &r) const {
			return (min > r.max) - (max < r.min);
		}
	};
	std::set<Range> ranges;
	CSet(WConv_Encoding) { }
	CSet &operator|=(const CSet &cs) {
		for (const auto &e : cs.ranges)
			set(e.min, e.max);
		return *this;
	}
#endif
	CSet &invert() {
#ifdef CHARSET
		int errcode = 0;
		charset_t *newset = charset_invert(charset, &errcode); // FIXME: no error checking
		charset_free(charset);
		charset = newset;
#else
		std::set<Range> nranges;
		WChar lo = 0;
		for (const auto &e : ranges) {
			if (lo < e.min)
				nranges.emplace(lo, e.min - 1);
			lo = e.max + 1;
		}
		if (lo <= WCharMax)
			nranges.emplace(lo, WCharMax);
		ranges = std::move(nranges);
#endif
		return *this;
	}
	CSet &set(WChar wclo, WChar wchi) {
#ifdef CHARSET
		charset_add_range(charset, wclo, wchi);	// FIXME: no error checking
#else
		auto e = Range(wclo - (wclo != std::numeric_limits<WChar>::min()), wchi + (wchi != std::numeric_limits<WChar>::max()));
		auto [x, y] = ranges.equal_range(e);
		if (x == y) {
			ranges.insert(Range(wclo, wchi));
		} else {
			if (x->max >= e.min)
				wclo = MIN(wclo, x->min);
			auto z = y;
			--z;
			if (z->min <= e.max)
				wchi = MAX(wchi, z->max);
			auto i = ranges.erase(x, y);
			ranges.insert(i, Range(wclo, wchi));
		}
#endif
		return *this;
	}
	CSet &set(WChar wc) {
#ifdef CHARSET
		charset_add_char(charset, wc);	// FIXME: no error checking
		return *this;
#else
		return set(wc, wc);
#endif
	}
	bool test(WChar wc) const {
#ifdef CHARSET
		return charset_in_set(charset, wc);
#else
		if (wc < 0)
			return false;
		auto i = ranges.lower_bound(Range(wc, wc));
		return i != ranges.end() && wc >= i->min && wc <= i->max;
#endif
	}
	bool cclass(minrx_regcomp_flags_t flags, WConv_Encoding enc, const std::string &name) {
#ifdef CHARSET
		int result = charset_add_cclass(charset, name.c_str());
		if ((flags & MINRX_REG_ICASE) != 0) {
			if (name == "lower")
				charset_add_cclass(charset, "upper");	// FIXME: Add error checking
			else if (name == "upper")
				charset_add_cclass(charset, "lower");	// FIXME: Add error checking
		}
		return result == CSET_SUCCESS;
#else
		auto wct = wctype(name.c_str());
		if (wct) {
			std::string key = name + ":" + setlocale(LC_CTYPE, NULL) + ":" + ((flags & MINRX_REG_ICASE) != 0 ? "1" : "0");
			std::lock_guard<std::mutex> lock(cclmutex);
			auto i = cclmemo.find(key);
			if (i == cclmemo.end()) {
				if (enc == Byte)
					for (WChar b = 0; b <= 0xFF; ++b) {
						if (iswctype(btowc(b), wct)) {
							set(b);
							if ((flags & MINRX_REG_ICASE) != 0) {
								set(tolower(b));
								set(toupper(b));
							}
						}
					}
				else
					for (WChar wc = 0; wc <= WCharMax; ++wc) {
						if (iswctype(wc, wct)) {
							set(wc);
							if ((flags & MINRX_REG_ICASE) != 0) {
								set(towlower(wc));
								set(towupper(wc));
							}
						}
					}
				cclmemo.emplace(key, *this);
				i = cclmemo.find(key);
			}
			*this |= i->second; // N.B. could probably be safely outside the critical section, since cclmemo entries are never deleted
			return true;
		}
		return false;
#endif
	}
#ifndef CHARSET
	void add_equiv(int32_t equiv) {
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
				set(u);
		}
	}
#endif
	minrx_result_t parse(minrx_regcomp_flags_t flags, WConv_Encoding enc, WConv &wconv) {
		WChar wc = wconv_nextchr(&wconv);
		bool inv = wc == L'^';
		if (inv)
			wc = wconv_nextchr(&wconv);
		for (bool first = true; first || wc != L']'; first = false) {
			if (wc == End)
				return MINRX_REG_EBRACK;
			WChar wclo = wc, wchi = wc;
			wc = wconv_nextchr(&wconv);
			if (wclo == L'\\' && (flags & MINRX_REG_BRACK_ESCAPE) != 0) {
				if (wc != End) {
					wclo = wchi = wc;
					wc = wconv_nextchr(&wconv);
				} else {
					return MINRX_REG_EESCAPE;
				}
			} else if (wclo == L'[') {
				if (wc == L'.') {
					wc = wconv_nextchr(&wconv);
					wclo = wchi = wc;
#ifdef CHARSET_NOT_YET
					int32_t coll[2] = { wc, L'\0' };
					charset_add_collate(charset, coll);	// FIXME: No error checking
					if ((flags & MINRX_REG_ICASE) != 0) {
						if (iswlower(wc))
							coll[0] = towupper(wc);
						else if (iswupper(wc))
							coll[0] = towlower(wc);
						charset_add_collate(charset, coll);	// FIXME: No error checking
					}
#endif
					wc = wconv_nextchr(&wconv);
					if (wc != L'.' || (wc = wconv_nextchr(&wconv)) != L']')
						return MINRX_REG_ECOLLATE;
					wc = wconv_nextchr(&wconv);
				} else if (wc == L':') {
					const char *bp = wconv_ptr(&wconv), *ep = bp;
					do
						ep = wconv_ptr(&wconv), wc = wconv_nextchr(&wconv);
					while (wc != End && wc != L':');
					if (wc != L':')
						return MINRX_REG_ECTYPE;
					wc = wconv_nextchr(&wconv);
					if (wc != L']')
						return MINRX_REG_ECTYPE;
					wc = wconv_nextchr(&wconv);
					auto cclname = std::string(bp, ep);
					if (cclass(flags, enc, cclname))
						continue;
					return MINRX_REG_ECTYPE;
				} else if (wc == L'=') {
					wc = wconv_nextchr(&wconv);
					wclo = wchi = wc;
#ifdef CHARSET
					charset_add_equiv(charset, wc);	// FIXME: No error checking
					if ((flags & MINRX_REG_ICASE) != 0) {
						if (iswlower(wc))
							charset_add_equiv(charset, towupper(wc));	// FIXME: no error checking
						else if (iswupper(wc))
							charset_add_equiv(charset, towlower(wc));	// FIXME: no error checking
					}
#else
					add_equiv(wc);
					if ((flags & MINRX_REG_ICASE) != 0) {
						if (iswlower(wc))
							add_equiv(towupper(wc));
						else if (iswupper(wc))
							add_equiv(towlower(wc));
					}
#endif
					wc = wconv_nextchr(&wconv);
					if (wc != L'=' || (wc = wconv_nextchr(&wconv)) != L']')
						return MINRX_REG_ECOLLATE;
				}
			}
			bool range = false;
			if (wc == L'-') {
				const char *save = wconv_save(&wconv);
				wc = wconv_nextchr(&wconv);
				if (wc == End)
					return MINRX_REG_EBRACK;
				if (wc != L']') {
					wchi = wc;
					wc = wconv_nextchr(&wconv);
					if (wchi == L'\\' && (flags & MINRX_REG_BRACK_ESCAPE) != 0) {
						if (wc != End) {
							wchi = wc;
							wc = wconv_nextchr(&wconv);
						} else {
							return MINRX_REG_EESCAPE;
						}
					} else if (wchi == L'[') {
						if (wc == L'.') {
							wchi = wconv_nextchr(&wconv);
							wc = wconv_nextchr(&wconv);
							if (wc != L'.' || (wc = wconv_nextchr(&wconv)) != L']')
								return MINRX_REG_ECOLLATE;
							wc = wconv_nextchr(&wconv);
						} else if (wc == L':' || wc == L'=') {
							return MINRX_REG_ERANGE; // can't be range endpoint
						}
					}
					range = true;
				} else {
					wconv_restore(&wconv, save);
					wc = L'-';
				}
			}
			if (wclo > wchi || (wclo != wchi && (wclo < 0 || wchi < 0)))
				return MINRX_REG_ERANGE;
			if (wclo >= 0) {
				set(wclo, wchi);
				if ((flags & MINRX_REG_ICASE) != 0) {
					for (WChar wc = wclo; wc <= wchi; ++wc) {
						set(enc == Byte ? tolower(wc) : towlower(wc));
						set(enc == Byte ? toupper(wc) : towupper(wc));
					}
				}
			}
			if (range && wc == L'-' && wconv_lookahead(&wconv) != L']')
				return MINRX_REG_ERANGE;
		}
		if (inv) {
			if ((flags & MINRX_REG_NEWLINE) != 0)
				set(L'\n');
			invert();
		}
		return MINRX_REG_SUCCESS;
	}
	static unsigned int utfprefix(WChar wc) {
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
	std::pair<std::optional<const std::array<bool, 256>>, std::optional<char>>
	firstbytes(WConv_Encoding e) const {
		std::array<bool, 256> fb = {};
		auto firstunique = [](const std::array<bool, 256> &fb) -> std::optional<char> {
			int n = 0, u = -1;
			for (int i = 0; i < 256; ++i)
				if (fb[i])
					++n, u = i;
			return n == 1 ? std::optional<char>(u) : std::optional<char>();
		};
		switch (e) {
		case Byte:
#ifdef CHARSET
		{
			int errcode = 0;
			charset_firstbytes_t bytes = charset_firstbytes(charset, &errcode);
			for (int i = 0; i < MAX_FIRSTBYTES; i++)
				fb[i] = bytes.bytes[i];
		}
#else
			for (const auto &r : ranges) {
				if (r.min > 255)
					break;
				auto lo = r.min, hi = MIN(255, r.max);
				for (auto b = lo; b <= hi; b++)
					fb[b] = true;
			}
#endif
			return {fb, firstunique(fb)};
		case UTF8:
#ifdef CHARSET
		{
			int errcode = 0;
			charset_firstbytes_t bytes = charset_firstbytes(charset, &errcode);
			for (int i = 0; i < MAX_FIRSTBYTES; i++)
				fb[i] = bytes.bytes[i];
		}
#else
			for (const auto &r : ranges) {
				auto lo = utfprefix(r.min), hi = utfprefix(r.max);
				for (auto b = lo; b <= hi; b++)
					fb[b] = true;
			}
#endif
			return {fb, firstunique(fb)};
		default:
			return {{}, {}};
		}
	}
};

#ifndef CHARSET
std::map<std::string, CSet> CSet::cclmemo;
std::mutex CSet::cclmutex;
#endif

typedef size_t NInt;

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
	WConv_Encoding enc;
	minrx_result_t err;
	const std::vector<CSet> csets;
	const Node *nodes;
	size_t nnode;
	std::optional<const CSet> firstcset;
	std::optional<const std::array<bool, 256>> firstbytes;
	std::optional<char> firstunique;
	size_t nmin;
	size_t nstk;
	size_t nsub;
	~Regexp() {
		free((void *) nodes);
	}
};

//
// The output of compiling is a malloced array of nodes, but while compiling
// we keep the future array elements in a singly-linked list to facilitate
// concatenation as well as element insertion at both ends.
//
typedef struct ListNode ListNode;	// Node wrapped in list element container.
typedef struct NodeList NodeList;	// List of nodes.
typedef struct NodePool NodePool;	// Pool of not-yet-allocated ListNodes.

struct ListNode {
	Node node;
	ListNode *next;
};

struct NodeList {
	ListNode *first;
	ListNode *final;
	NInt size;
};

#define NALLOC 25
struct NodePool {
	int nalloc;
	NodePool *prev;
	ListNode nodes[NALLOC];
};

static ListNode *
alloc(NodePool **npp, NInt type, NInt arg0, NInt arg1, NInt nstk)
{
	ListNode *n;
	if (!*npp || (*npp)->nalloc == NALLOC) {
		NodePool *np = (NodePool *) malloc(sizeof (NodePool));
		if (!np)
			return nullptr;
		np->nalloc = 0;
		np->prev = *npp;
		*npp = np;
	}
	n = &(*npp)->nodes[(*npp)->nalloc++];
	n->node.type = type;
	n->node.args[0] = arg0;
	n->node.args[1] = arg1;
	n->node.nstk = nstk;
	return n;
}

static bool
concatcopy(NodePool **npp, NodeList *x, const NodeList *y)
{
	for (auto n = y->first; n; n = n->next) {
		auto nn = alloc(npp, n->node.type, n->node.args[0], n->node.args[1], n->node.nstk);
		if (!nn)
			return false;
		if (x->size++)
			x->final->next = nn;
		else
			x->first = nn;
		x->final = nn;
		nn->next = nullptr;
	}
	return true;
}

static void
concatmove(NodeList *x, const NodeList *y)
{
	if (x->size) {
		if (y->size)
			x->final->next = y->first, x->final = y->final, x->size += y->size;
	} else {
		*x = *y;
	}
}

static bool
emplace_first(NodePool **npp, NodeList *x, NInt type, NInt arg0, NInt arg1, NInt nstk)
{
	ListNode *n = alloc(npp, type, arg0, arg1, nstk);
	if (!n)
		return false;
	if (x->size++) {
		n->next = x->first;
		x->first = n;
	} else {
		n->next = nullptr;
		x->first = x->final = n;
	}
	return true;
}

static bool
emplace_final(NodePool **npp, NodeList *x, NInt type, NInt arg0, NInt arg1, NInt nstk)
{
	ListNode *n = alloc(npp, type, arg0, arg1, nstk);
	if (!n)
		return false;
	if (x->size++)
		x->final->next = n;
	else
		x->first = n;
	x->final = n;
	n->next = nullptr;
	return true;
}

static NodeList
empty()
{
	NodeList r;
	r.first = nullptr;
	r.final = nullptr;
	r.size = 0;
	return r;
}

struct Compile {
	const minrx_regcomp_flags_t flags;
	WConv_Encoding enc;
	WConv wconv;
	WChar wc;
	std::vector<CSet> csets;
	std::optional<size_t> dot;
	std::optional<size_t> esc_s;
	std::optional<size_t> esc_S;
	std::optional<size_t> esc_w;
	std::optional<size_t> esc_W;
	std::map<WChar, unsigned int> icmap;
	NInt nmin = 0;
	NInt nsub = 0;
	NodePool *np = 0;
	Compile(WConv_Encoding e, const char *bp, const char *ep, minrx_regcomp_flags_t flags): flags(flags), enc(e) {
		wconv_construct(&wconv, e, bp, ep);
		wc = wconv_nextchr(&wconv);
	}
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
					wc = wconv_nextchr(&wconv);
				while (wc >= L'0' && wc <= L'9');
				n = -1;
				return true;
			}
			wc = wconv_nextchr(&wconv);
		} while (wc >= L'0' && wc <= L'9');
		n = v;
		return true;
	}
	typedef std::tuple<NodeList, size_t, bool, minrx_result_t> Subexp;
	Subexp alt(bool nested, NInt nstk) {
		auto [lhs, lhmaxstk, lhasmin, err] = cat(nested, nstk);
		if (err)
			return {lhs, lhmaxstk, lhasmin, err};
		if (wc == L'|') {
			for (auto l = lhs.first; l != nullptr; l = l->next)
				l->node.nstk += 1;
			std::vector<Subexp> alts;
			while (wc == L'|') {
				wc = wconv_nextchr(&wconv);
				alts.push_back(cat(nested, nstk + 1));
			}
			auto [rhs, rhmaxstk, rhasmin, err] = alts.back();
			if (err)
				return {rhs, rhmaxstk, rhasmin, err};
			if (!emplace_first(&np, &rhs, Node::Goto, rhs.size, rhs.size + 1, nstk + 1))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			alts.pop_back();
			while (!alts.empty()) {
				auto [mhs, mhmaxstk, mhasmin, _] = alts.back();
				alts.pop_back();
				auto mhsize = mhs.size;
				concatmove(&mhs, &rhs);
				rhmaxstk = MAX(mhmaxstk, rhmaxstk);
				rhasmin |= mhasmin;
				rhs = mhs;
				if (!emplace_first(&np, &rhs, Node::Goto, mhsize, rhs.size + 1, nstk + 1))
					return {empty(), 0, false, MINRX_REG_ESPACE};
			}
			if (!emplace_first(&np, &lhs, Node::Fork, lhs.size, 0, nstk + 1))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			concatmove(&lhs, &rhs);
			lhmaxstk = MAX(lhmaxstk, rhmaxstk);
			lhasmin |= rhasmin;
			if (!emplace_final(&np, &lhs, Node::Join, lhs.size - 1, 0, nstk + 1))
				return {empty(), 0, false, MINRX_REG_ESPACE};
		}
		return {lhs, lhmaxstk, lhasmin, MINRX_REG_SUCCESS};
	}
	Subexp cat(bool nested, NInt nstk) {
		auto [lhs, lhmaxstk, lhasmin, err] = rep(nested, nstk);
		if (err)
			return {lhs, lhmaxstk, lhasmin, err};
		while (wc != End && wc != L'|' && (wc != L')' || !nested)) {
			auto [rhs, rhmaxstk, rhasmin, err] = rep(nested, nstk);
			if (err)
				return {rhs, rhmaxstk, rhasmin, err};
			concatmove(&lhs, &rhs);
			lhmaxstk = MAX(lhmaxstk, rhmaxstk);
			lhasmin |= rhasmin;
		}
		return {lhs, lhmaxstk, lhasmin, MINRX_REG_SUCCESS};
	}
	Subexp minimize(const Subexp &lh, NInt nstk) {
		if (std::get<minrx_result_t>(lh))
			return lh;
		auto [nodes, maxstk, hasmin, err] = lh;
		for (auto n = nodes.first; n != nullptr; n = n->next)
			n->node.nstk += 1;
		if (!emplace_first(&np, &nodes, Node::MinL, 0, 0, nstk + 1) || !emplace_final(&np, &nodes, Node::MinR, 0, 0, nstk))
			return {empty(), 0, false, MINRX_REG_ESPACE};
		nmin = MAX(nmin, (size_t) 1);
		return {nodes, maxstk + 1, true, err};
	}
	void minraise(Subexp &lh) {
		if (std::get<minrx_result_t>(lh))
			return;
		auto &[nodes, maxstk, hasmin, err] = lh;
		NInt maxlevel = 0;
		for (auto n = nodes.first; n != nullptr; n = n->next)
			switch (n->node.type) {
			case Node::MinB:
			case Node::MinL:
			case Node::MinR:
				maxlevel = MAX(maxlevel, ++n->node.args[0]);
				break;
			default:
				;
			}
		nmin = MAX(nmin, maxlevel + 1);
	}
	Subexp mkrep(const Subexp &lh, bool optional, bool infinite, NInt nstk) {
		if (std::get<minrx_result_t>(lh))
			return lh;
		auto [lhs, lhmaxstk, lhasmin, err] = lh;
		if (optional && !infinite) {
			for (auto l = lhs.first; l != nullptr; l = l->next)
				l->node.nstk += 2;
			auto lhsize = lhs.size;
			if (!emplace_first(&np, &lhs, Node::Skip, lhsize, 0, nstk + 2))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			return {lhs, lhmaxstk + 2, lhasmin, MINRX_REG_SUCCESS};
		} else {
			for (auto l = lhs.first; l != nullptr; l = l->next)
				l->node.nstk += 3;
			auto lhsize = lhs.size;
			if (!emplace_first(&np, &lhs, Node::Loop, lhsize, (NInt) optional, nstk + 3) || !emplace_final(&np, &lhs, Node::Next, lhsize, (NInt) infinite, nstk))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			return {lhs, lhmaxstk + 3, lhasmin, MINRX_REG_SUCCESS};
		}
	}
	Subexp mkrep(const Subexp &lh, NInt m, NInt n, NInt nstk) {
		if (std::get<minrx_result_t>(lh))
			return lh;
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
		lhs = empty();
		if (!concatcopy(&np, &lhs, &rhs))	// force initial lhs to be a copy
			return {empty(), 0, false, MINRX_REG_ESPACE};
		for (k = 1; k < m; ++k)
			if (!concatcopy(&np, &lhs, &rhs))
				return {empty(), 0, false, MINRX_REG_ESPACE};
		if (n != (NInt) -1 && k < n) {
			lhmaxstk += 2;
			rhmaxstk += 2;
			for (auto r = rhs.first; r != nullptr; r = r->next)
				r->node.nstk += 2;
			auto rhsize = rhs.size;
			if (!emplace_first(&np, &rhs, Node::Skip, rhsize, 1, nstk + 2))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			for (; k < n; ++k)
				if (!concatcopy(&np, &lhs, &rhs))
					return {empty(), 0, false, MINRX_REG_ESPACE};
		}
		if (n == (NInt) -1) {
			lhmaxstk += 3;
			rhmaxstk += 3;
			for (auto r = rhs.first; r != nullptr; r = r->next)
				r->node.nstk += 3;
			auto rhsize = rhs.size;
			if (!emplace_first(&np, &rhs, Node::Loop, rhsize, 1, nstk + 3) || !emplace_final(&np, &rhs, Node::Next, rhsize, 1, nstk))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			concatmove(&lhs, &rhs);
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
			common:	if ((flags & MINRX_REG_MINDISABLE) == 0 && (wc = wconv_nextchr(&wconv)) == L'?')
					minimal ^= true, wc = wconv_nextchr(&wconv);
				if (hasmin)
					minraise(lh);
				lh = mkrep(minimal ? minimize(lh, nstk) : lh, optional, infinite, nstk);
			comout:	if (minimal) {
					if (!emplace_first(&np, &std::get<0>(lh), Node::MinB, 0, 0, nstk))
						return {empty(), 0, false, MINRX_REG_ESPACE};
					hasmin = true;
				}
				std::get<bool>(lh) = hasmin;
				continue;
			case L'{':
				if ((flags & MINRX_REG_BRACE_COMPAT) == 0
				    || (enc == Byte ? isdigit(wconv_lookahead(&wconv)) : IsDigit(wconv_lookahead(&wconv))))
				{
					wc = wconv_nextchr(&wconv);
					if (wc == End)
						return {{}, 0, false, MINRX_REG_EBRACE};
					NInt m, n;
					if (!num(m, wc))
						return {{}, 0, false, MINRX_REG_BADBR};
					if (wc == L'}') {
						if ((flags & MINRX_REG_MINDISABLE) == 0 && (wc = wconv_nextchr(&wconv)) == L'?')
							minimal ^= true, wc = wconv_nextchr(&wconv);
						if (hasmin)
							minraise(lh);
						lh = mkrep(minimal ? minimize(lh, nstk) : lh, m, m, nstk);
						goto comout;
					}
					if (wc == End)
						return {{}, 0, false, MINRX_REG_EBRACE};
					if (wc != L',')
						return {{}, 0, false, MINRX_REG_BADBR};
					wc = wconv_nextchr(&wconv);
					if (wc == L'}') {
						if ((flags & MINRX_REG_MINDISABLE) == 0 && (wc = wconv_nextchr(&wconv)) == L'?')
							minimal ^= true, wc = wconv_nextchr(&wconv);
						if (hasmin)
							minraise(lh);
						lh = mkrep(minimal ? minimize(lh, nstk) : lh, m, -1, nstk);
						goto comout;
					}
					if (!num(n, wc))
						return {{}, 0, false, MINRX_REG_BADBR};
					if (wc == End)
						return {{}, 0, false, MINRX_REG_EBRACE};
					if (wc != L'}')
						return {{}, 0, false, MINRX_REG_BADBR};
					if ((flags & MINRX_REG_MINDISABLE) == 0 && (wc = wconv_nextchr(&wconv)) == L'?')
						minimal ^= true, wc = wconv_nextchr(&wconv);
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
		NodeList lhs = empty();
		size_t lhmaxstk;
		bool lhasmin = false;
		switch (wc) {
		default:
		normal:
			lhmaxstk = nstk;
			if ((flags & MINRX_REG_ICASE) == 0) {
				if (!emplace_first(&np, &lhs, (NInt) wc, 0, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
			} else {
				WChar wcl = enc == Byte ? tolower(wc) : towlower(wc);
				WChar wcu = enc == Byte ? toupper(wc) : towupper(wc);
				if (wc != wcl || wc != wcu) {
					auto key = MIN(wc, MIN(wcl, wcu));
					if (icmap.find(key) == icmap.end()) {
						icmap.emplace(key, csets.size());
						csets.emplace_back(enc);
						csets.back().set(wc);
						csets.back().set(wcl);
						csets.back().set(wcu);
					}
					if (!emplace_final(&np, &lhs, Node::CSet, icmap[key], 0, nstk))
						return {empty(), 0, false, MINRX_REG_ESPACE};
				} else {
					if (!emplace_final(&np, &lhs, (NInt) wc, 0, 0, nstk))
						return {empty(), 0, false, MINRX_REG_ESPACE};
				}
			}
			wc = wconv_nextchr(&wconv);
			break;
		case L'{':
			if ((flags & MINRX_REG_BRACE_COMPAT) != 0
			    && (enc == Byte ? !isdigit(wconv_lookahead(&wconv)) : !IsDigit(wconv_lookahead(&wconv))))
				goto normal;
			// fall through
		case L'*':
		case L'+':
		case L'?':
			return {empty(), 0, false, MINRX_REG_BADRPT};
		case L'[':
			lhmaxstk = nstk;
			if (!emplace_final(&np, &lhs, Node::CSet, csets.size(), 0, nstk))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			if (auto err = csets.emplace_back(enc).parse(flags, enc, wconv))
				return {empty(), 0, false, err};
			wc = wconv_nextchr(&wconv);
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
			if (!emplace_final(&np, &lhs, Node::CSet, *dot, 0, nstk))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			wc = wconv_nextchr(&wconv);
			break;
		case L'^':
			lhmaxstk = nstk;
			if (!emplace_final(&np, &lhs, (flags & MINRX_REG_NEWLINE) == 0 ? Node::ZBOB : Node::ZBOL, 0, 0, nstk))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			wc = wconv_nextchr(&wconv);
			break;
		case L'$':
			lhmaxstk = nstk;
			if (!emplace_final(&np, &lhs, (flags & MINRX_REG_NEWLINE) == 0 ? Node::ZEOB : Node::ZEOL, 0, 0, nstk))
				return {empty(), 0, false, MINRX_REG_ESPACE};
			wc = wconv_nextchr(&wconv);
			break;
		case L'\\':
			lhmaxstk = nstk;
			wc = wconv_nextchr(&wconv);
			switch (wc) {
			case L'<':
				if ((flags & MINRX_REG_EXTENSIONS_BSD) == 0)
					goto normal;
				if (!emplace_final(&np, &lhs, Node::ZBOW, 0, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L'>':
				if ((flags & MINRX_REG_EXTENSIONS_BSD) == 0)
					goto normal;
				if (!emplace_final(&np, &lhs, Node::ZEOW, 0, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L'`':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!emplace_final(&np, &lhs, Node::ZBOB, 0, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L'\'':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!emplace_final(&np, &lhs, Node::ZEOB, 0, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L'b':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!emplace_final(&np, &lhs, Node::ZXOW, 0, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L'B':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!emplace_final(&np, &lhs, Node::ZNWB, 0, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L's':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!esc_s.has_value()) {
					esc_s = csets.size();
					WConv wc;
					wconv_constructz(&wc, enc, "[:space:]]");
					csets.emplace_back(enc).parse(flags, enc, wc);
				}
				if (!emplace_final(&np, &lhs, Node::CSet, *esc_s, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L'S':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!esc_S.has_value()) {
					esc_S = csets.size();
					WConv wc;
					wconv_constructz(&wc, enc, "^[:space:]]");
					csets.emplace_back(enc).parse(flags, enc, wc);
				}
				if (!emplace_final(&np, &lhs, Node::CSet, *esc_S, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L'w':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!esc_w.has_value()) {
					esc_w = csets.size();
					WConv wc;
					wconv_constructz(&wc, enc, "[:alnum:]_]");
					csets.emplace_back(enc).parse(flags, enc, wc);
				}
				if (!emplace_final(&np, &lhs, Node::CSet, *esc_w, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case L'W':
				if ((flags & MINRX_REG_EXTENSIONS_GNU) == 0)
					goto normal;
				if (!esc_W.has_value()) {
					esc_W = csets.size();
					WConv wc;
					wconv_constructz(&wc, enc, "^[:alnum:]_]");
					csets.emplace_back(enc).parse(flags, enc, wc);
				}
				if (!emplace_final(&np, &lhs, Node::CSet, *esc_W, 0, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				break;
			case End:
				return {{}, 0, false, MINRX_REG_EESCAPE};
			default:
				goto normal;
			}
			wc = wconv_nextchr(&wconv);
			break;
		case L'(':
			{
				NInt n = ++nsub;
				wc = wconv_nextchr(&wconv);
				minrx_result_t err;
				std::tie(lhs, lhmaxstk, lhasmin, err) = alt(true, nstk + 1);
				if (err)
					return {lhs, lhmaxstk, lhasmin, err};
				if (wc != L')')
					return {{}, 0, false, MINRX_REG_EPAREN};
				if (!emplace_first(&np, &lhs, Node::SubL, n, nsub, nstk + 1) || !emplace_final(&np, &lhs, Node::SubR, n, nsub, nstk))
					return {empty(), 0, false, MINRX_REG_ESPACE};
				wc = wconv_nextchr(&wconv);
			}
			break;
		case L')':
			if (!nested)
				goto normal;
			// fall through
		case L'|':
		case End:
			lhmaxstk = nstk;
			break;
		}
		return {lhs, lhmaxstk, lhasmin, MINRX_REG_SUCCESS};
	}
	std::optional<CSet> firstclosure(const Node *nodes, NInt nnode) {
		if (nnode == 0)
			return {};
		QSet epsq, epsv, firsts;
		if (!qset_construct(&epsq, nnode))
			return {};
		if (!qset_construct(&epsv, nnode)) {
			qset_destruct(&epsq);
			return {};
		}
		if (!qset_construct(&firsts, nnode)) {
			qset_destruct(&epsq);
			qset_destruct(&epsv);
			return {};
		}
		auto add = [&epsq, &epsv](NInt n) { if (!qset_contains(&epsv, n)) { qset_insert(&epsq, n); qset_insert(&epsv, n); } };
		qset_insert(&epsq, 0);
		do {
			auto k = qset_remove(&epsq);
			auto &n = nodes[k];
			if (n.type <= Node::CSet)
				qset_insert(&firsts, k);
			else
				switch (n.type) {
				case Node::Exit:
					qset_destruct(&firsts);
					qset_destruct(&epsv);
					qset_destruct(&epsq);
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
		} while (!qset_empty(&epsq));
		CSet cs(enc);
		while (!qset_empty(&firsts)) {
			auto k = qset_remove(&firsts);
			auto t = nodes[k].type;
			if (t <= WCharMax)
				cs.set(t);
			else
				cs |= csets[nodes[k].args[0]];
		}
		qset_destruct(&firsts);
		qset_destruct(&epsv);
		qset_destruct(&epsq);
		return cs;
	}
	std::pair<std::optional<const std::array<bool, 256>>, std::optional<char>>
	firstbytes(WConv_Encoding e, const std::optional<CSet>& firstcset) {
		if (!firstcset.has_value())
			return {};
		return firstcset->firstbytes(e);
	}
	Regexp *compile() {
		Node *nodes = nullptr;
		NInt nnode = 0;
		if ((flags & MINRX_REG_MINDISABLE) != 0 && (flags & MINRX_REG_MINIMAL) != 0)
			return new Regexp { enc, MINRX_REG_BADPAT, {}, nullptr, 0, {}, {}, {}, 0, 0, 1 };
		auto [lhs, nstk, hasmin, err] = alt(false, 0);
		if (!err && (!emplace_final(&np, &lhs, Node::Exit, 0, 0, 0) || !(nodes = (Node *) malloc(lhs.size * sizeof (Node)))))
			err = MINRX_REG_ESPACE;
		if (err) {
			csets.clear();
			lhs = empty();
			nmin = 0;
			nstk = 0;
			nsub = 0;
		}
		if (nmin > 0)
			for (auto l = lhs.first; l; l = l->next)
				l->node.nstk += nmin;
		for (auto l = lhs.first; l; l = l->next)
			nodes[nnode++] = l->node;
		for (auto p = np, q = p; p; p = q) {
			q = p->prev;
			free((void *) p);
		}
		np = nullptr;
		auto fc = firstclosure(nodes, nnode);	// FIXME: check for allocation errors
		auto [fb, fu] = firstbytes(enc, fc);	// FIXME: check for allocation errors
		return new Regexp{ enc, err, std::move(csets), nodes, nnode, std::move(fc), std::move(fb), std::move(fu), nmin, nstk, nsub + 1 };
	}
};

static const size_t SizeBits = std::numeric_limits<size_t>::digits;

struct Execute {
	const Regexp *r;
	minrx_regexec_flags_t flags;
	const Node *nodes;
	size_t suboff;
	size_t minvcnt;
	size_t minvoff;
	size_t nestoff;
	size_t gen;
	size_t off;
	WConv wconv;
	WChar wcprev;
	COWVec_Allocator allocator;
	COWVec best;
	NInt bestmincount; // note mincounts are negated so this means +infinity
	QSet epsq;
	QVec epsv;
};

static void
execute_construct(Execute *e, const Regexp *r, minrx_regexec_flags_t flags, const char *bp, const char *ep)
{
	e->r = r;
	e->flags = flags;
	e->nodes = r->nodes;
	e->suboff = r->nmin + r->nstk;
	e->minvcnt = (r->nmin + SizeBits - 1) / SizeBits;
	e->minvoff = e->suboff + 2 * r->nsub;
	e->nestoff = e->minvoff + e->minvcnt;
	e->gen = 0;
	e->off = 0;
	wconv_construct(&e->wconv, r->enc, bp, ep);
	e->wcprev = End;
	cowvec_allocator_construct(&e->allocator, e->nestoff + r->nmin);
	cowvec_construct(&e->best, nullptr);
	e->bestmincount = 0;
	if (!qset_construct(&e->epsq, r->nnode))
		throw std::bad_alloc();
	qvec_construct(&e->epsv, r->nnode);
}

static void
execute_destruct(Execute *e)
{
	qvec_destruct(&e->epsv);
	qset_destruct(&e->epsq);
	cowvec_destruct(&e->best);
	cowvec_allocator_destruct(&e->allocator);
}

template <typename... XArgs>
inline static void
execute_add(Execute *e, QVec &ncsv, NInt k, NInt nstk, const NState *nsp, WChar wcnext, XArgs... xargs)
{
	const Node &n = e->nodes[k];
	if (n.type <= Node::CSet) {
		if (n.type == (NInt) wcnext || (n.type == Node::CSet && e->r->csets[n.args[0]].test(wcnext))) {
			auto [newly, newnsp] = qvec_insert(&ncsv, k, nsp);
			if (newly)
				new (newnsp) NState(*nsp), nstate_construct_copy(newnsp, nsp);
			else if (auto x = nstate_cmp(nsp, newnsp, e->gen, nstk, xargs...); x > 0 || (x == 0 && e->minvcnt && cowvec_cmp_from(e->minvoff, &nsp->substack, &newnsp->substack, e->minvcnt) > 0))
				nstate_copy(newnsp, nsp);
			else
				return;
			newnsp->gen = e->gen;
			if constexpr (sizeof... (XArgs) > 0) {
				auto i = nstk - sizeof...(XArgs);
				(cowvec_put(&newnsp->substack, i++, xargs), ...);
			}
		}
	} else {
		auto [newly, newnsp] = qvec_insert(&e->epsv, k, nsp);
		if (newly)
			new (newnsp) NState(*nsp), nstate_construct_copy(newnsp, nsp);
		else if (auto x = nstate_cmp(nsp, newnsp, e->gen, nstk, xargs...); x > 0 || (x == 0 && e->minvcnt && cowvec_cmp_from(e->minvoff, &nsp->substack, &newnsp->substack, e->minvcnt) > 0))
			nstate_copy(newnsp, nsp);
		else
			return;
		newnsp->gen = e->gen;
		if constexpr (sizeof... (XArgs) > 0) {
			auto i = nstk - sizeof...(XArgs);
			(cowvec_put(&newnsp->substack, i++, xargs), ...);
		}
		qset_insert(&e->epsq, k);
	}
}

static void
execute_epsclosure(Execute *e, QVec &ncsv, WChar wcnext)
{
	auto nodes = e->nodes;
	auto is_word = e->r->enc == Byte ? [](WChar b) { return b == '_' || isalnum(b); }
					 : [](WChar wc) { return wc == L'_' || iswalnum(wc); };
	do {
		NInt k = qset_remove(&e->epsq);
		NState *nsp = qvec_lookup(&e->epsv, k);
		if (cowvec_valid(&e->best) && nsp->boff > cowvec_get(&e->best, e->suboff + 0))
			continue;
		const auto &n = e->nodes[k];
		auto nstk = n.nstk;
		switch (n.type) {
		case Node::Exit:
			{
				auto beg = nsp->boff, end = e->off, mincount = e->r->nmin ? cowvec_get(&nsp->substack, 0) : (NInt) -1;
				bool minvalid = e->r->nmin ? cowvec_get(&nsp->substack, e->minvoff) < ((size_t) 1 << (SizeBits - 1)) : false;
				if (!cowvec_valid(&e->best)
				    || beg < cowvec_get(&e->best, e->suboff + 0)
				    || (beg == cowvec_get(&e->best, e->suboff + 0) && end > cowvec_get(&e->best, e->suboff + 1) && (!minvalid || mincount >= e->bestmincount)))
				{
					cowvec_copy(&e->best, &nsp->substack);
					cowvec_put(&e->best, e->suboff + 0, beg);
					cowvec_put(&e->best, e->suboff + 1, end);
					if (minvalid)
						e->bestmincount = MAX(e->bestmincount, mincount);
				}
			}
			break;
		case Node::Fork:
			{
				NInt priority = (NInt) -1;
				do {
					execute_add(e, ncsv, k + 1, nstk, nsp, wcnext, priority--);
					k = k + 1 + nodes[k].args[0];
				} while (nodes[k].type != Node::Join);
			}
			break;
		case Node::Goto:
			execute_add(e, ncsv, k + 1 + n.args[1], nstk, nsp, wcnext);
			break;
		case Node::Join:
			execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		case Node::Loop:
			execute_add(e, ncsv, k + 1, nstk, nsp, wcnext, (NInt) e->off, (NInt) -1, (NInt) e->off);
			if (n.args[1])
				execute_add(e, ncsv, k + 1 + n.args[0], nstk, nsp, wcnext, (NInt) e->off, (NInt) 0, (NInt) e->off);
			break;
		case Node::MinB:
			{
				size_t w = n.args[0] / SizeBits;
				size_t b = (size_t) 1 << (SizeBits - 1 - n.args[0] % SizeBits);
				NState nscopy;
				nstate_construct_copy(&nscopy, nsp);
				b |= -b;
				auto x = cowvec_get(&nscopy.substack, e->minvoff + w);
				do {
					if ((x & b) != 0)
						cowvec_put(&nscopy.substack, e->minvoff + w, x & ~b);
					b = -1;
				} while ( w-- > 0);
				execute_add(e, ncsv, k + 1, nstk, &nscopy, wcnext);
				nstate_destruct(&nscopy);
			}
			break;
		case Node::MinL:
			execute_add(e, ncsv, k + 1, nstk, nsp, wcnext, e->off);
			break;
		case Node::MinR:
			{
				NState nscopy;
				nstate_construct_copy(&nscopy, nsp);
				auto mininc = e->off - cowvec_get(&nscopy.substack, n.nstk);
				size_t oldlen = (size_t) -1 - cowvec_get(&nscopy.substack, n.args[0]);
				mininc -= cowvec_get(&nscopy.substack, e->nestoff + n.args[0]);
				cowvec_put(&nscopy.substack, e->nestoff + n.args[0], 0);
				cowvec_put(&nscopy.substack, n.args[0], (size_t) -1 - (oldlen + mininc));
				for (auto i = n.args[0]; i-- > 0; ) {
					oldlen = (size_t) -1 - cowvec_get(&nscopy.substack, i);
					cowvec_put(&nscopy.substack, i, -1 - (oldlen + mininc));
					cowvec_put(&nscopy.substack, e->nestoff + i, cowvec_get(&nscopy.substack, e->nestoff + i) + mininc);
				}
				execute_add(e, ncsv, k + 1, nstk, &nscopy, wcnext);
				nstate_destruct(&nscopy);
			}
			break;
		case Node::Next:
			execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			if (n.args[1] && e->off > cowvec_get(&nsp->substack, nstk + 3 - 1))
				execute_add(e, ncsv, k - n.args[0], nstk + 3, nsp, wcnext, cowvec_get(&nsp->substack, nstk), cowvec_get(&nsp->substack, nstk + 1) - 1, (NInt) e->off);
			break;
		case Node::Skip:
			execute_add(e, ncsv, k + 1, nstk, nsp, wcnext, (NInt) e->off, (NInt) 1 ^ n.args[1]);
			execute_add(e, ncsv, k + 1 + n.args[0], nstk, nsp, wcnext, (NInt) e->off, (NInt) 0 ^ n.args[1]);
			break;
		case Node::SubL:
			{
				NState nscopy;
				nstate_construct_copy(&nscopy, nsp);
				cowvec_put(&nscopy.substack, nstk - 1, e->off);
				if (n.args[0] != (NInt) -1 && (e->flags & MINRX_REG_NOSUBRESET) == 0)
					for (auto i = n.args[0] + 1; i <= n.args[1]; ++i) {
						cowvec_put(&nscopy.substack, e->suboff + i * 2, -1);
						cowvec_put(&nscopy.substack, e->suboff + i * 2 + 1, -1);
					}
				execute_add(e, ncsv, k + 1, nstk, &nscopy, wcnext);
				nstate_destruct(&nscopy);
			}
			break;
		case Node::SubR:
			if (n.args[0] != (NInt) -1 && ((e->flags & MINRX_REG_FIRSTSUB) == 0 || cowvec_get(&nsp->substack, e->suboff + n.args[0] * 2) == (NInt) -1)) {
				NState nscopy;
				nstate_construct_copy(&nscopy, nsp);
				cowvec_put(&nscopy.substack, e->suboff + n.args[0] * 2 + 0, cowvec_get(&nsp->substack, nstk));
				cowvec_put(&nscopy.substack, e->suboff + n.args[0] * 2 + 1, e->off);
				execute_add(e, ncsv, k + 1, nstk, &nscopy, wcnext);
				nstate_destruct(&nscopy);
			} else {
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			}
			break;
		case Node::ZBOB:
			if (e->off == 0 && (e->flags & MINRX_REG_NOTBOL) == 0)
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		case Node::ZEOB:
			if (wcnext == End && (e->flags & MINRX_REG_NOTEOL) == 0)
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		case Node::ZBOL:
			if (((e->off == 0 && (e->flags & MINRX_REG_NOTBOL) == 0)) || e->wcprev == L'\n')
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		case Node::ZEOL:
			if (((wcnext == End && (e->flags & MINRX_REG_NOTEOL) == 0)) || wcnext == L'\n')
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		case Node::ZBOW:
			if ((e->off == 0 || !is_word(e->wcprev)) && (wcnext != End && is_word(wcnext)))
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		case Node::ZEOW:
			if ((e->off != 0 && is_word(e->wcprev)) && (wcnext == End || !is_word(wcnext)))
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		case Node::ZXOW:
			if (   ((e->off == 0 || !is_word(e->wcprev)) && (wcnext != End && is_word(wcnext)))
			    || ((e->off != 0 && is_word(e->wcprev)) && (wcnext == End || !is_word(wcnext))))
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		case Node::ZNWB:
			if (   (e->off == 0 && wcnext == End)
			    || (e->off == 0 && wcnext != End && !is_word(wcnext))
			    || (e->off != 0 && !is_word(e->wcprev) && wcnext == End)
			    || (e->off != 0 && wcnext != End && is_word(e->wcprev) == is_word(wcnext)))
				execute_add(e, ncsv, k + 1, nstk, nsp, wcnext);
			break;
		default:
			abort();
			break;
		}
	} while (!qset_empty(&e->epsq));
}

static int
execute(Execute *e, size_t nm, minrx_regmatch_t *rm)
{
	QVec mcsvs[2];
	qvec_construct(&mcsvs[0], e->r->nnode);
	qvec_construct(&mcsvs[1], e->r->nnode);
	e->off = wconv_off(&e->wconv);
	auto wcnext = wconv_nextchr(&e->wconv);
	if ((e->flags & MINRX_REG_RESUME) != 0 && rm && rm[0].rm_eo > 0)
		while (wcnext != End && (ptrdiff_t) e->off < rm[0].rm_eo)
			e->wcprev = wcnext, e->off = wconv_off(&e->wconv), wcnext = wconv_nextchr(&e->wconv);
	NState nsinit;
	nstate_construct(&nsinit, &e->allocator);
	if ((e->flags & MINRX_REG_NOFIRSTBYTES) == 0 && e->r->firstbytes.has_value() && !e->r->firstcset->test(wcnext)) {
	zoom:
		auto cp = e->wconv.cp, ep = e->wconv.ep;
		if (e->r->firstunique.has_value()) {
			cp = (const char *) memchr(cp, *e->r->firstunique, ep - cp);
			if (cp == nullptr)
				goto exit;
		} else {
			auto firstbytes = *e->r->firstbytes;
			while (cp != ep && !firstbytes[(unsigned char) *cp])
				++cp;
			if (cp == ep)
				goto exit;
		}
		if (cp != e->wconv.cp) {
			if (e->r->enc == UTF8) {
				auto bp = cp;
				while (bp != e->wconv.cp && cp - bp < 8 && (unsigned char) *--bp >= 0x80)
					;
				e->wconv.cp = (unsigned char) *bp >= 0x80 ? cp - 1 : bp;
			} else {
				e->wconv.cp = cp - 1;
			}
			wcnext = wconv_nextchr(&e->wconv);
		}
		++e->gen, e->wcprev = wcnext, e->off = wconv_off(&e->wconv), wcnext = wconv_nextchr(&e->wconv);
	}
	nsinit.boff = e->off;
	for (size_t i = 0; i < e->r->nmin; ++i)
		cowvec_put(&nsinit.substack, e->nestoff + i, 0);
	execute_add(e, mcsvs[0], 0, 0, &nsinit, wcnext);
	if (!qset_empty(&e->epsq))
		execute_epsclosure(e, mcsvs[0], wcnext);
	for (;;) { // unrolled to ping-pong roles of mcsvs[0]/[1]
		if (wcnext == End)
			break;
		++e->gen;
		e->wcprev = wcnext, e->off = wconv_off(&e->wconv), wcnext = wconv_nextchr(&e->wconv);
		while (!qvec_empty(&mcsvs[0])) {
			auto [n, ns] = qvec_remove(&mcsvs[0]);
			execute_add(e, mcsvs[1], n + 1, e->nodes[n].nstk, &ns, wcnext);
			nstate_destruct(&ns);
		}
		if (!cowvec_valid(&e->best)) {
			nsinit.boff = e->off;
			execute_add(e, mcsvs[1], 0, 0, &nsinit, wcnext);
		}
		if (!qset_empty(&e->epsq))
			execute_epsclosure(e, mcsvs[1], wcnext);
		if (qvec_empty(&mcsvs[1])) {
			if (cowvec_valid(&e->best))
				break;
			if ((e->flags & MINRX_REG_NOFIRSTBYTES) == 0 && e->r->firstbytes.has_value())
				goto zoom;
		}
		if (wcnext == End)
			break;
		++e->gen;
		e->wcprev = wcnext, e->off = wconv_off(&e->wconv), wcnext = wconv_nextchr(&e->wconv);
		while (!qvec_empty(&mcsvs[1])) {
			auto [n, ns] = qvec_remove(&mcsvs[1]);
			execute_add(e, mcsvs[0], n + 1, e->nodes[n].nstk, &ns, wcnext);
			nstate_destruct(&ns);
		}
		if (!cowvec_valid(&e->best)) {
			nsinit.boff = e->off;
			execute_add(e, mcsvs[0], 0, 0, &nsinit, wcnext);
		}
		if (!qset_empty(&e->epsq))
			execute_epsclosure(e, mcsvs[0], wcnext);
		if (qvec_empty(&mcsvs[0])) {
			if (cowvec_valid(&e->best))
				break;
			if ((e->flags & MINRX_REG_NOFIRSTBYTES) == 0 && e->r->firstbytes.has_value())
				goto zoom;
		}
	}
exit:
	nstate_destruct(&nsinit);
	qvec_destruct(&mcsvs[1]);
	qvec_destruct(&mcsvs[0]);
	if (cowvec_valid(&e->best)) {
		if (rm) {
			size_t nsub = MIN(nm, e->r->nsub);
			size_t i;
			for (i = 0; i < nsub; ++i) {
				rm[i].rm_so = cowvec_get(&e->best, e->suboff + i * 2);
				rm[i].rm_eo = cowvec_get(&e->best, e->suboff + i * 2 + 1);
			}
			for (; i < nm; ++i)
				rm[i].rm_so = rm[i].rm_eo = -1;
		}
		return 0;
	} else {
		if (rm)
			for (size_t i = 0; i < nm; ++i)
				rm[i].rm_so = rm[i].rm_eo = -1;
		return MINRX_REG_NOMATCH;
	}
}

}

int
minrx_regcomp(minrx_regex_t *rx, const char *s, int flags)
{
	return minrx_regncomp(rx, strlen(s), s, flags);
}

int
minrx_regexec(minrx_regex_t *rx, const char *s, size_t nm, minrx_regmatch_t *rm, int flags)
{
	return minrx_regnexec(rx, strlen(s), s, nm, rm, flags);
}

int
minrx_regncomp(minrx_regex_t *rx, size_t ns, const char *s, int flags)
{
	auto enc = MinRX::MBtoWC;
	auto loc = setlocale(LC_CTYPE, nullptr);
	if ((strcmp(loc, "C") == 0 || strcmp(loc, "POSIX") == 0 ||
		(flags & MINRX_REG_NATIVE1B) != 0) && MB_CUR_MAX == 1)
		enc = MinRX::Byte;
	else if (strcmp(nl_langinfo(CODESET), "UTF-8") == 0)
		enc = MinRX::UTF8;
	auto r = MinRX::Compile(enc, s, s + ns, (minrx_regcomp_flags_t) flags).compile();
	rx->re_regexp = r;
	rx->re_nsub = r->nsub - 1;
	rx->re_compflags = (minrx_regcomp_flags_t) flags;
	return r->err;
}

int
minrx_regnexec(minrx_regex_t *rx, size_t ns, const char *s, size_t nm, minrx_regmatch_t *rm, int flags)
{
	MinRX::Regexp *r = reinterpret_cast<MinRX::Regexp *>(rx->re_regexp);
	MinRX::Execute e;
	MinRX::execute_construct(&e, r, (minrx_regexec_flags_t) flags, s, s + ns);
	int ret = MinRX::execute(&e, nm, rm);
	MinRX::execute_destruct(&e);
	return ret;
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
