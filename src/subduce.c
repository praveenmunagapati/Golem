/* ####################################################################### */

/*                      GOLEM deduction by atom subsumption		   */
/*                      -----------------------------------		   */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

ITEM ct_subduce();
ITEM ct_subduces();
ITEM cl_vrenum();
LIST *cl_subduce1();
LONG cl_vmax();

/*
 * cl_subduce/2 - returns the set of substitutions into the clause
 *	for atoms from "as" which can be proved using "clause". It is
 *	expected that the clause will be determinate and well-ordered.
 */

ITEM
cl_subduce(clause,as,lim)
	LONG lim;
	ITEM clause,as;
	{
	ITEM head,sub0,subs,presub,oldsub,bas,atom,oldsub1,atom1,
		as1=b_sample(lim,as),psym,subs1,sub;
	LIST *last;
	LONG nvars=0l,lcnt=0l;
	PREDICATE ndeterm;
	register LIST elem1,*elem2,oldelem;
	register LONG anum;
	PREDICATE deleted;
	nvars=cl_vmax(clause);
	subs=ct_subduce(head=l_pop(clause),
		sub0=i_create('f',(POINTER)f_zero(f_create(nvars+2))),as1);
	psym=F_ELEM(0l,head);
/*
	ndeterm=b_memq((LONG)I_GET(psym),nondeterm);
*/
	ndeterm=TRUE;
	i_delete(as1);
	if(ndeterm) {
	  last=L_LAST(subs1=L_EMPTY);
	  LIST_DO(sub,subs)
	    last=cl_subduce1((LIST)I_GET(clause),sub,last);
	  LIST_END
	  i_delete(subs);
	  subs=subs1;
	}
	else {
	 LIST_LOOP(elem1,(LIST)I_GET(clause)) {
	  LISTP_LOOP(elem2,subs) {
	    do {
	      deleted=FALSE;
	      ct_subduce1(atom=L_GET(elem1),presub=
			L_GET(oldelem= *elem2),bas=b_copy(bbacks));
	      switch(b_size(bas)) {
		/* Should be case 0 or 1 unless literal has
			2 variables the same, eg. f(A,B,A) */
		case 0: *elem2= oldelem->next; i_delete(presub);
		    L_DEL(oldelem,"cl_subduce"); deleted=TRUE;
		    break;
		case 1:
		    if(!ct_match(atom,atom1=b_elem(anum=b_first(bas),spatoms),presub)) {
			*elem2= oldelem->next; i_delete(presub);
			L_DEL(oldelem,"cl_subduce"); deleted=TRUE;
		    }
		    else b_add(anum,F_ELEM(1l,presub));
		    I_DEC(atom1);
		    break;
		default: {
		    register ITEM *sarr=((FUNC)I_GET(
		      *(((FUNC)I_GET(spatoms))->arr)))->arr;
		    PREDICATE matched=FALSE;
		    anum=0l;
		    BIT_DO(anum,bas)
		      oldsub=f_copy(presub);
		      if(matched) {
		        if(ct_match(atom,sarr[anum],oldsub1=f_copy(oldsub))) {
			  l_push(head,clause);
		          i_deletes(head,sub0,subs,oldsub,
			    bas,oldsub1,(ITEM)I_TERM);
		          return((ITEM)NULL);  /* Non-determinate clause */
		        }
		        else i_delete(oldsub1);
		      }
		      else if(ct_match(atom,sarr[anum],presub))
		        {b_add(anum,F_ELEM(1l,presub)); matched=TRUE;}
		      else i_swap(oldsub,presub);
		      i_delete(oldsub);
		    BIT_END
		    if(!matched) {*elem2= oldelem->next; i_delete(presub);
		      L_DEL(oldelem,"cl_subduce"); deleted=TRUE;}
		}
	      }
	      i_delete(bas);
	    } while(deleted && *elem2);
	    if(!(*elem2)) break;
	  }
	 }
	}
	l_push(head,clause);
	i_deletes(head,sub0,(ITEM)I_TERM);
	return(subs);
}

/*
 * cl_subduce1/3 - depth-first interpretaion of clause. This
 *	is more space efficient than breadth-first interpretation
 *	for non-determinate clauses.
 */

LIST *ct_subduce0();

LIST *
cl_subduce1(lits,sub,last)
	LIST lits;
	ITEM sub;
	LIST *last;
	{
	ITEM subs1,lit;
	register LIST *last1,*oldlast=last,elem;
	if(lits) {
	    ct_subduce0(lit=L_GET(lits),sub,bbacks,FALSE,
		last1=L_LAST(subs1=L_EMPTY));
	    if(dostats) cl_substats(lit,sub,l_length(subs1));
	    lits=lits->next;
	    LIST_LOOP(elem,(LIST)I_GET(subs1)) {
		last=cl_subduce1(lits,L_GET(elem),last);
		if(last!=oldlast) break;
	    }
	    i_delete(subs1);
	}
	else last=l_end(i_inc(sub),last);
	return(last);
}

/*
 * ct_subduces/3 - returns the set of substitutions for atoms in "as"
 *	subsumed by the given atom for all given substitutions.
 */


ITEM
ct_subduces(atom,subs,bas)
	ITEM atom,subs,bas;
	{
	ITEM result;
	LIST elem,*last=L_LAST(result=L_EMPTY);
	LIST_LOOP(elem,(LIST)I_GET(subs))
	    last=ct_subduce0(atom,L_GET(elem),bas,FALSE,last);
	return(result);
}

/*
 * ct_subduce/3 - returns the set of substitutions for atoms in "as"
 *	subsumed by the given atom.
 */

ITEM
ct_subduce(atom,subst,as)
	ITEM atom,subst,as;
	{
	ITEM result;
	LIST *last;
	ct_subduce0(atom,subst,as,TRUE,last=L_LAST(result=L_EMPTY));
	return(result);
}

LIST *ct_vclash();

LIST *
ct_subduce0(atom,subst,as,adda,last)
	ITEM atom,subst,as;
	LIST *last;
	PREDICATE adda;
	{
	register ITEM as1=b_copy(as),result,*fptr;
	register FUNC f=(FUNC)I_GET(atom);
	ARG_LOOP(fptr,f) ct_subduce1(*fptr,subst,as1);
	last=ct_vclash(atom,subst,as1,adda,last);
	i_delete(as1);
	return(last);
}

/*
 * ct_subduce1/3 - given atom(A),substitution(S) and atom bitset(B),
 *	destructively reduces B to B1 such that B1 subset B and A subsumes
 *	all A1 in B1 up to substitution clash.
 */

int
ct_subduce1(term,subst,as)
	ITEM term,subst,as;
	{
	register FUNC f;
	register ITEM *fptr,sterm,lptas,as1;
	register LONG tv,ptv,*pt,pv;

	if ((tv=TNO(ptv=(term->extra)))==NGRND) switch(term->item_type) {
	  case 'f':
	    f=(FUNC)I_GET(term);
	    ARG_LOOP(fptr,f) ct_subduce1(*fptr,subst,as);
	    break;
	  case 'v':
	    if(sterm=F_ELEM(((LONG)I_GET(term))+2,subst)) {
		if(*(pt=pt_ins(PNO(ptv),TNO(sterm->extra)))!=PTTERM)
		    b_int(as,F_ELEM(GETPT(pt),ptas));
		else {
		    i_delete(as);
		    as=B_EMPTY;
		}
	    }
	    else {
		if(!(lptas=i_inc(F_ELEM(PNO(ptv),pas)))) lptas=B_EMPTY;
		b_int(as,lptas);
		i_delete(lptas);
	    }
	    break;
	  default:
	    d_error("ct_subduce1 - bad term type");
	}
	else if (hpt[HPT(pv=PNO(ptv),tv)]) {
	    FNDPT(pv,tv,pt);
	    b_int(as,F_ELEM(GETPT(pt),ptas));
	}
	else {
	    i_swap(as,as1=B_EMPTY);
	    i_delete(as1);
	}
}

/*
 * ct_vclash - creates new substitutions which are supersets
 *	of the given subst. for every atom in bas which matches
 *	atom. This requires resolving variable clashes. The
 *	flag "adda" is used to decide whether to add the
 *	matched atom as the 0th element of the substitution.
 */

LIST *
ct_vclash(atom,subst,bas,adda,last)
	ITEM atom,subst,bas;
	PREDICATE adda;
	LIST *last;
	{
	ITEM as,subst1,atom1;
	register LIST elem;
	if(b_emptyq(bas)) return(last);
	as=b_btos(spatoms,bas);
	LIST_LOOP(elem,(LIST)I_GET(as)) {
	    if(ct_match(atom,atom1=L_GET(elem),subst1=f_copy(subst))) {
		if(adda) {
		    F_ELEM(0l,subst1)=i_inc(atom1);
		    F_ELEM(1l,subst1)=B_EMPTY;
		}
		last=l_end(subst1,last);
	    }
	    else i_delete(subst1);
	}
	i_delete(as);
	return(last);
}

/*
 * ct_match/3 - one-sided unification of terms
 */

PREDICATE
ct_match(t1,t2,subst)
	ITEM t1,t2,subst;
	{
	if(TNO(t1->extra)==NGRND) switch(t1->item_type) {
	  case 'f': {
		  register FUNC f1=(FUNC)I_GET(t1),
			f2=(FUNC)I_GET(t2);
		  register ITEM *fptr1,*fptr2;
		  if (t2->item_type!='f') return(FALSE);
		  ARG_LOOP2(fptr1,fptr2,f1,f2)
		    if (!ct_match(*fptr1,*fptr2,subst))
			return(FALSE);
		}
		break;
	  case 'v': {
		  ITEM t;
		  if (t=F_ELEM(((LONG)I_GET(t1))+2,subst)) {
		    if (TNO(t->extra)!=TNO(t2->extra))
		      return(FALSE);
		  }
		  else F_ELEM(((LONG)I_GET(t1))+2,subst)=i_inc(t2);
		}
		break;
	  default:	/* 'h','i','r' */
		d_error("ct_match - bad term type");
	}
	return(TRUE);
}

ITEM ct_vrenum();

ITEM
cl_vrenum(clause,nvars)
	ITEM clause;
	LONG *nvars;
	{
	ITEM hvars=h_create(4l),result;
	LIST elem,*last=L_LAST(result=L_EMPTY);
	LIST_LOOP(elem,(LIST)I_GET(clause))
	    last=l_end(ct_vrenum(L_GET(elem),nvars,hvars),last);
	i_delete(hvars);
	return(result);
}

ITEM
ct_vrenum(term,nvars,hvars)
	ITEM term,hvars;
	LONG *nvars;
	{
	ITEM result;
	register FUNC f1,f2;
	register ITEM *fptr1,*fptr2,*entry;
	switch(term->item_type) {
	    case 'f':
		f2=(FUNC)I_GET(term);
		result=i_create('f',(POINTER)(f1=f_create(f2->arr_size)));
		result->extra=term->extra;
		FNAME(f1)= i_inc(FNAME(f2));
		ARG_LOOP2(fptr1,fptr2,f1,f2)
			*fptr1=ct_vrenum(*fptr2,nvars,hvars);
		break;
	    case 'v':
		if(!(*(entry=h_ins(term,hvars))))
			*entry=i_create('i',(POINTER)(*nvars)++);
		result=i_create('v',(POINTER)I_GET(*entry));
		result->extra=term->extra;
		break;
	    case 'h': case 'i': case 'r':
		result=i_inc(term);
		break;
	    default:
		d_error("ct_vrenum - bad term type");
	}
	return(result);
}

/*
 * cl_substats/3 - keeps statistics of instantiations and numbers
 *	of matches for clause ordering purposes. The set of places
 *	in the literal in which variables are open wrt the substitution
 *	are hashed to update the average number of matches for such a literal.
 *	Average is stored as a single number An. Updates are done according
 *	to the formula An+1 = (c.An + Vn)/(c+1) where Vn is the latest
 *	number of matches.
 */

#define LOGW 3
#define NEWAV(a,v,l)	((a)=(((a)*((1l<<(l))-1l)+(v))>>(l)))

LIST *cl_substats1();

int
cl_substats(lit,sub,matches)
	ITEM lit,sub;
	LONG matches;
	{
	ITEM *entry,places;
	LIST *last;
	LONG intentry;

	if(!matches) return;
	cl_substats1(lit,sub,last=L_LAST(places=L_EMPTY));
	if(!(*(entry=h_ins(i_sort(places),substats)))) *entry=I_INT(matches);
	else {
		intentry = ((LONG)((*entry)->obj));
/*
		NEWAV((LONG)I_GET(*entry),matches,LOGW);
*/
		NEWAV((LONG)intentry,matches,LOGW);
	}
	i_delete(places);
}

LIST *
cl_substats1(term,sub,last)
	ITEM term,sub;
	LIST *last;
	{
	switch(term->item_type) {
	    case 'f': {
		FUNC f=(FUNC)I_GET(term);
		ITEM *fptr;
		ARG_LOOP(fptr,f) last=cl_substats1(*fptr,sub,last);
	      }
	      break;
	    case 'v': {
	        if(!F_ELEM(((LONG)I_GET(term))+2,sub))
		    last=l_end(I_INT(PNO(term->extra)),last);
	      }
	      break;
	    case 'h': case 'i': case 'r':
	      break;
	    default:
		d_error("cl_substats1 - bad term type");
	}
	return(last);
}

/* cl_vmax(clause) - returns the maximum variable + 1
 */
LONG ct_vmax();

LONG
cl_vmax(clause)
	ITEM clause;
	{
	LONG vmax=0l,vmax1;
	ITEM atom;
	LIST_DO(atom,clause)
	  if((vmax1=ct_vmax(atom))>vmax) vmax=vmax1;
	LIST_END
	return(vmax+1l);
}

LONG
ct_vmax(term)
	ITEM term;
	{
	LONG vmax=0l,vmax1;
	FUNC f;
	ITEM *fptr;
	switch(term->item_type) {
	  case 'f':
	    f=(FUNC)I_GET(term);
	    ARG_LOOP(fptr,f)
	      if((vmax1=ct_vmax(*fptr))>vmax) vmax=vmax1;
	    break;
	  case 'v':
	    if((vmax1=(LONG)I_GET(term))>vmax) vmax=vmax1;
	    break;
	  case 'i': case 'h': case 'r':
	    break;
	  default: d_error("ct_vmax - bad term");
	}
	return(vmax);
}
