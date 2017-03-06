/* ####################################################################### */

/*                      GOLEM Patch Operations				   */
/*                      ----------------------------                       */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/*
 * Patches are a useful representation for combinatoric spaces. The idea
 *	is as follows. You are given the combinatoric space A*B*C where A,B,C are
 *	sets. Instead of representing this space explicitly by all individual
 *	tuples in the cross product, we simply represent it by the tuple
 *	of sets <A,B,C>. Now A1*..*An /\ B1*..*Bn = (A1/\B1)*..*(An/\Bn).
 *	So we can interesect combinatoric spaces by simply intersecting
 *	the sets representing the dimensions of the spaces. Also
 *	A1*..*An <= B1*..*Bn iff A1<=B1 and .. and An<=Bn. So subspace
 *	can be checked simply by considering dimensions again. We
 *	call this implicit repsentation of a combinatoric space a patch
 *	and talk of intersection and subpatch as operators on patches.
 */

/*
 * ptc_reduce/1 - given a set of patches P. For any pair of patches p1,p2
 *	in P st. p1 <= p2, p1 is removed. The operation is destructive.
 *	Patch Reduction algorithm
 *	~~~~~~~~~~~~~~~~~~~~~~~~~
 *	Given Patches = <<E11,..,E1n>,..,<Em1,..,Emn>>
 *		where Elements = \/(E11,..,E1n,..,Em1,..,Emn)
 *	Construct mapping Patch(e,i):(Elements*{1,.,n}) -> 2^{1,..,m}
 *	For each <Ei1,..,Ein> in Patches Do
 *	    RedundantPatches=Patches-{Eij}
 *	    For each Eij in <Ei1,..,Ein> Do
 *	    	For each e in Eij Do
 *		    RedundantPatches /\= Patch(e,j)
 *	    Patches -= RedundantPatches
 */


ITEM
ptc_reduce(patches)
	ITEM patches;
	{
	ITEM inverse=ptc_inverse(patches,FALSE),
		bpatches=b_allones(l_length(patches)),redpatches,
		fpatches=f_ltof(patches),result;
	register ITEM elem,*sarr,patch,s1,s2;
	register LONG e1,i,j;
	register LIST *last=L_LAST(result=L_EMPTY);
	i=0l;
	BIT_DO(i,bpatches)
	    patch=F_ELEM(i,fpatches); j=0l;
	    redpatches=b_copy(bpatches);
	    LIST_DO(elem,patch)
		e1=0l;
		BIT_DO(e1,elem)
		    if((s1=F_ELEM(e1,inverse))&&(s2=F_ELEM(j,s1)))
			b_int(redpatches,s2);
		    else {i_delete(redpatches);redpatches=B_EMPTY;}
		BIT_END
		j++;
	    LIST_END
	    b_sub(bpatches,b_rem(i,redpatches));
	    i_delete(redpatches);
	BIT_END
	sarr=((FUNC)I_GET(fpatches))->arr;
	BIT_DO(sarr,bpatches)
	    last=l_end(i_inc(*sarr),last);
	BIT_END
	i_swap(patches,result);
	i_deletes(inverse,bpatches,fpatches,result,(ITEM)I_TERM);
	return(patches);
}

/*
 * ptc_inverse/2 - given Patches = <<E11,..,E1n>,..,<Em1,..,Emn>>
 *		where Elements = \/(E11,..,E1n,..,Em1,..,Emn)
 *	Construct mapping Patch(e,i):(Elements*{1,.,n}) -> 2^{1,..,m}
 *	If complement is true then each set in 2^{1,..,m} is represented
 *	by its complement.
 */

ITEM
ptc_inverse(patches,complement)
	ITEM patches;
	PREDICATE complement;
	{
	ITEM result=i_create('f',f_zero(f_create(64l))),*entry1,*entry2;
	register LONG i,e,n,j,m;
	register ITEM elem1,elem2;
	if(complement) m=l_length(patches);
	if(!L_EMPTYQ(patches)) n=l_length(HOF((LIST)I_GET(patches)));
	j=0l;
	LIST_DO(elem1,patches)
	    i=0l;
	    LIST_DO(elem2,elem1)
		e=0l;
		BIT_DO(e,elem2)
		    if(!(*(entry1=f_ins(e,result))))
			*entry1=i_create('f',f_zero(f_create(n)));
		    if(!(*(entry2=f_ins(i,*entry1))))
			*entry2=(complement?b_allones(m):B_EMPTY);
		    if(complement) b_rem(j,*entry2);
		    else b_add(j,*entry2);
		BIT_END
		i++;
	    LIST_END
	    j++;
	LIST_END
	return(result);
}

/*
 * ct_null(patches) - destructively filters out null patches
 */

ptc_null(patches)
	ITEM patches;
	{
	register LIST *elem1,elem2;
	register ITEM elem;
	for(elem1=L_LAST(patches);*elem1;) {
	    ITEM patch=L_GET(*elem1);
	    PREDICATE null=FALSE;
	    LIST_DO(elem,patch)
		if(b_emptyq(elem)) {null=TRUE; break;}
	    LIST_END
	    if (null) { /* null patch */
		elem2= *elem1;
		*elem1= (*elem1)->next;
		i_delete(L_GET(elem2));
		L_DEL(elem2,"ptc_null");
	    }
	    else elem1= &((*elem1)->next);
	}
}
