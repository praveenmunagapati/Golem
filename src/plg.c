/* ####################################################################### */

/*                      GOLEM Quintus Prolog interface			   */
/*                      ------------------------------			   */

/* ####################################################################### */

/*
 * Predicate/function symbol to number conversion. Used
 *	to contain Quintus Prolog interface.
 */

#include <stdio.h>
#include "golem.h"

STRING
QP_ntos(n)
	LONG n;
	{
	ITEM *entry;
#ifdef MEMCHECK
	if (!spsyms) return("**");
#endif
	return((STRING)I_GET(F_ELEM(0l,F_ELEM(n,F_ELEM(0l,spsyms)))));
}

/*
 * QP_ston/2 - gets unique number for function-symbol/arity
 *	pair. This is different from O'Keefe's term package, which
 *	maps each function-symbol to a unique number.
 */

LONG
QP_ston(s,n)
	STRING s;
	LONG n;
	{
	ITEM snum=i_tup2(i_dec(i_create('s',(POINTER)strsave(s))),
			i_dec(I_INT(n)));
	LONG result=b_num(snum,spsyms);
	i_delete(snum);
	return(result);
}
