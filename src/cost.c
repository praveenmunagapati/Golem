/* ####################################################################### */

/*                      GOLEM Cterm Cost Functions			   */
/*                      --------------------------			   */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/***************************************************************************
 * ct_cost/1 - gives the cost of a term calculated as follows
 *		variable - 1
 *		term - 2 + sumi(cost(argi))
 *		constant - 2
 *		integer - 2
 *		real - 2
 */

float ct_cost1();

LONG
ct_cost(term)
	ITEM term;
	{
	register LONG result;
	switch(term->item_type) {
	    case 'f': {
		  register FUNC f=(FUNC)I_GET(term);
		  register ITEM *fptr;
		  result=2;
		  ARG_LOOP(fptr,f) result += ct_cost(*fptr);
	        }
	        break;
	    case 'h': case 'r':
		result=2l;
		break;
	    case 'i': {
		register LONG v=((LONG)I_GET(term));
		v=(v<0?-v+1:v+1);
		/* result=LOG2(v)+1l; */
		result=v;
		}
		break;
	    case 'v':
		result=1l;
		break;
	    default:
		d_error("ct_cost - bad term type");
	}
	return(result);
}

/* cl_cost/1 - the cost of a clause is sumi(cost(literali))
 */

LONG
cl_cost(cl)
	ITEM cl;
	{
	register ITEM elem;
	register LONG result=0l;
	LIST_DO(elem,cl)
	    result += ct_cost(elem);
	LIST_END
	return(result);
}

/* cl_costs/1 - the cost of a set of clauses is sumi(cost(clausei))
 */

LONG
cl_costs(cls)
	ITEM cls;
	{
	register ITEM cl;
	register LONG result=0l;
	LIST_DO(cl,cls)
	    result += cl_cost(cl);
	LIST_END
	return(result);
}
