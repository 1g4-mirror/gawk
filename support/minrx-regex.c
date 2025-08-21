#ifdef __GNUC__
#define INLINE __attribute__((__always_inline__)) inline
#else
#define INLINE inline
#endif

#include "awk.h"	// sigh

#ifdef HAVE_CONFIG_H
#include "config.h"
#endif /* HAVE_CONFIG_H */

#include "minrx.h"

struct fake {
	struct re_pattern_buffer pat;
	struct re_registers regs;
};

static reg_syntax_t syn;


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
	if (do_posix)
		syn = RE_SYNTAX_POSIX_AWK;	/* strict POSIX re's */
	else if (do_traditional)
		syn = RE_SYNTAX_AWK;		/* traditional Unix awk re's */
	else
		syn = RE_SYNTAX_GNU_AWK;

	if (do_traditional)
		syn |= RE_INTERVALS | RE_INVALID_INTERVAL_ORD | RE_NO_BK_BRACES;

	struct fake *fake = (struct fake *) malloc(sizeof(struct fake));
	memset(fake, 0, sizeof(*fake));

	fake->pat.allocated = 0;
	fake->pat.fastmap = (char *) malloc(256);

	if ((flags & MINRX_REG_ICASE) != 0) {
		if (gawk_mb_cur_max > 1) {
			syn |= RE_ICASE;
			fake->pat.translate = NULL;
		} else {
			syn &= ~RE_ICASE;
			fake->pat.translate = (RE_TRANSLATE_TYPE) casetable;
		}
	} else {
		fake->pat.translate = NULL;
		syn &= ~RE_ICASE;
	}

	(void) re_set_syntax(syn);

	const char *rerr;
	if ((rerr = re_compile_pattern(s, ns, &(fake->pat))) != NULL) {
		free(fake);
		return MINRX_REG_BADPAT;	// xxx
	}
	fake->pat.newline_anchor = false;

	rx->re_regexp = fake;
	rx->re_nsub = 255;
	rx->re_compflags = (minrx_regcomp_flags_t) flags;
	return MINRX_REG_SUCCESS;
}

int
minrx_regnexec(minrx_regex_t *rx, size_t ns, const char *s, size_t nm, minrx_regmatch_t *rm, int flags)
{
	int res, i;
	struct fake *fake = (struct fake *) rx->re_regexp;
	bool not_bol = (flags & MINRX_REG_NOTBOL) != 0;
	int start = 0;

	if (not_bol)
		fake->pat.not_bol = 1;

	if ((flags & MINRX_REG_RESUME) != 0 && rm != NULL && rm[0].rm_eo > 0)
		start = rm[0].rm_eo;

	res = re_search(&(fake->pat), s, start + ns, start, ns, rm != NULL ? & fake->regs : NULL);

	if (res >= 0)
		res = 0;

	fake->pat.not_bol = 0;

	if (rm != NULL) {
		for (i = 0; i < fake->regs.num_regs; i++) {
			rm[i].rm_so = fake->regs.start[i];
			rm[i].rm_eo = fake->regs.end[i];
		}
	}

	return res;
}

void
minrx_regfree(minrx_regex_t *rx)
{
	if (rx == NULL || rx->re_regexp == NULL)
		return;

	struct fake *fake = (struct fake *) rx->re_regexp;
	fake->pat.translate = NULL;
	regfree(& fake->pat);
	if (fake->regs.start)
		free(fake->regs.start);
	if (fake->regs.end)
		free(fake->regs.end);
	free(fake);
	rx->re_regexp = NULL;
}

size_t
minrx_regerror(int errcode, const minrx_regex_t *rx, char *errbuf, size_t errsize)
{
	struct fake *fake = (struct fake *) rx->re_regexp;

	return regerror(errcode, & fake->pat, errbuf, errsize);
}
