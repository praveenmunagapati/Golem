#include <stdio.h>
#include "golem.h"

/*
 * #######################################################################
 *
 *			Clause reduction Routines
 *                      -------------------------
 *
 * #######################################################################
 */

/*
 * cl_creduce/3 - reduces clause to minimal closed clause. Every literal
 *	which contains a variable not found in any other literal
 *	is removed.
 */

ITEM cl_vlits();

ITEM
cl_creduce(clause)
	ITEM clause;
	{
	LONG ndel;
	ITEM newclause=l_copy(clause),
		head=i_inc(HOF((LIST)I_GET(newclause))),
		oneh=l_push(head,L_EMPTY),dels,sing,
		litss1=cl_vlits(i_sort(newclause)),litss2;
	register LIST *last,elem;
	set_sub(i_sort(newclause),oneh);	/* No tautologies */
	do {
	  last=L_LAST(dels=L_EMPTY);
	  litss2=L_EMPTY;
	  while(!L_EMPTYQ(litss1)) {
	    if (l_length(sing=l_pop(litss1))==1)
	      last=l_end(i_inc(HOF((LIST)I_GET(sing))),last);
	    else l_push(sing,litss2);
	    i_delete(sing);
	  }
	  ndel=l_length(set_sub(i_sort(dels),oneh));
	  set_sub(newclause,dels);
	  LIST_LOOP(elem,(LIST)I_GET(litss2))
	    set_sub(L_GET(elem),dels);
	  i_deletes(dels,litss1,(ITEM)I_TERM);
	  litss1=i_sort(litss2);
	} while(ndel);
	l_push(head,newclause);
	i_deletes(head,litss1,oneh,(ITEM)I_TERM);
	return(newclause);
}

ITEM
cl_vlits(clause)
	ITEM clause;
	{
	ITEM hvl=h_create(5l),lit,*felem,result;
	register LIST elem,*last=L_LAST(result=L_EMPTY);
	FUNC f;
	LIST_LOOP(elem,(LIST)I_GET(clause))
		cl_vlits1(L_GET(elem),L_GET(elem),hvl);
	f=(FUNC)I_GET(hvl);
	FUNC_LOOP(felem,f)
	  if (*felem) LIST_LOOP(elem,(LIST)I_GET(*felem))
	    last=l_end(i_inc(i_sort(F_ELEM(1l,L_GET(elem)))),last);
	i_delete(hvl);
	return(i_sort(result));
}

int
cl_vlits1(term,lit,hvl)
	ITEM term,lit,hvl;
	{
	switch(term->item_type) {
	  case 'f':
	    {
	      register ITEM *fptr;
	      ARG_LOOP(fptr,(FUNC)I_GET(term))
		cl_vlits1(*fptr,lit,hvl);
	    }
	    break;
	  case 'v':
	    {
	      ITEM *entry;
	      if (!(*(entry=h_ins(term,hvl)))) *entry=L_EMPTY;
	      l_push(lit,*entry);
	    }
	    break;
	  case 'h': case 'i': case 'r':
	    break;
	  default:
	  d_error("cl_vlits1 - bad term type");
	}
}

ITEM cl_compset();
/*
 * cl_freduce - removes all literals which are unnecessary for
 *	computing functional I/O relationship. Returns NULL
 *	if no such relation can be computed. The functional
 *	relation is built up using hfmap to represent the
 *	dependency lattice of variables.
 */

ITEM cl_norep(),cl_fmap();

ITEM
cl_freduce(head,body)
	ITEM head,body;
	{
	ITEM ivars,ovars,unit,result,
		used,vars,ignorev,cl,newcl,hvis,
		hused=h_create(4l),*entry,hfmap=h_create(4l);
	LIST elem1,elem2,*last=L_LAST(result=L_EMPTY);
	PREDICATE first=TRUE;
	set_sub(i_sort(body),unit=l_push(head,L_EMPTY));
		/* Remove tautologies */
	cl_fmap(body,hfmap);
	cl_ioterms(unit,ivars=L_EMPTY,ovars=L_EMPTY,
		(ITEM)NULL,FALSE,FALSE,TRUE);
	vars=set_sub(set_sub(cl_vars(body),set_sub(ovars,ivars)),ivars);
	l_push((ITEM)NULL,vars); /* Don't ignore any */
	LIST_LOOP(elem1,(LIST)I_GET(vars)) {
	 ignorev=L_GET(elem1);
	 if (!first && !(*(h_ins(ignorev,hused))))
	   continue;
	 first=FALSE;
	 cl=L_EMPTY;
	 LIST_LOOP(elem2,(LIST)I_GET(ovars)) {
	  if (!(used=cl_compset(L_GET(elem2),ivars,	
		ignorev,hfmap,hvis=h_create(4l),hused))) {
	    i_delete(hvis);
	    break;
	  }
	  l_append(cl,l_reverse(used));
	  i_deletes(used,hvis,(ITEM)I_TERM);
	 }
	 if (!used) i_delete(cl);
	 else {
	   last=l_end(newcl=cl_norep(cl),last);
	   i_delete(cl);
	 }
	 /* break; */
	}
	i_deletes(hfmap,hused,vars,unit,ivars,ovars,(ITEM)I_TERM);
	return(i_sort(result));
}

/*
 * cl_compset/3 - find a set of literals that computes the
 *	given variable from the input variables. Uses the
 *	dependency graph hfmap to do so. Loops are detected
 *	using hvis, a hash table of visited variables.
 */

ITEM
cl_compset(var,ivars,ignorev,hfmap,hvis,hused)
	ITEM var,ivars,ignorev,hfmap,hvis,hused;
	{
	ITEM result=(ITEM)NULL,*entry,rec,lit,subvars,
		newlits,subvar,newres;
	LIST elem1,elem2;
	/* printf("  cl_compset variable - @%d\n",(int)I_GET(var)); */
	if (*(entry=h_ins(var,hvis))) {
		/* printf("  Fail (visited) - @%d\n",(int)I_GET(var)); */
		return((ITEM)NULL);
	}
	else *entry=i_inc(var);	/* Detect loop */
	if (*(entry=h_ins(var,hfmap))) {
	  LIST_LOOP(elem1,(LIST)I_GET(*entry)) { /* OR */
	    lit=F_ELEM(0l,rec=L_GET(elem1));
	    subvars=(set_sub(l_copy(F_ELEM(1l,rec)),ivars));
	    if (L_EMPTYQ(subvars)) {
	      i_deletes(subvars,result,(ITEM)I_TERM);
	      h_del(var,hvis);
	      if (!(*(entry=h_ins(var,hused)))) *entry=i_inc(var);
	      /* printf("  Succeeds (No subvars) - @%d\n",(int)I_GET(var)); */
	      return(l_push(lit,L_EMPTY));
	    }
	    i_delete(result);
	    result=L_EMPTY;
	    LIST_LOOP(elem2,(LIST)I_GET(subvars)) { /* AND */
	      if (ITMEQ(subvar=L_GET(elem2),ignorev) ||
		  !(newlits=cl_compset(subvar,ivars,ignorev,
			hfmap,hvis,hused))) {
		i_delete(result);
		result=L_EMPTY;
		break;
	      }
	      l_append(result,newlits);
	      i_delete(newlits);
	    }
	    i_delete(subvars);
	    if (!L_EMPTYQ(result)) {
		l_push(lit,result);
		break;
	    }
	  }
	  if (L_EMPTYQ(result)) {
	    i_delete(result);
	    result=(ITEM)NULL;
	  }
	  else if (!(*(entry=h_ins(var,hused)))) {
	      *entry=i_inc(var);
	  }
	}
	/* if (result) printf("  Succeeds (Recursively) - @%d\n",(int)I_GET(var));
	else printf("  Fails (Recursively) - @%d\n",(int)I_GET(var)); */
	h_del(var,hvis);
	return(result);
}

/*
 * cl_fmap/1 - constructs a functional mapping for all
 *	output variables (O) computed using particular literals (L)
 *	from some set of input variables (Is). This is
 *	returned as a hash table, keyed on O. Each hash
 *	record looks like [O [L Is]].
 */

ITEM
cl_fmap(body,hfmap)
	ITEM body,hfmap;
	{
	ITEM unit=L_EMPTY,ivars,ovars,lit,*entry,
		lvpair,both,*fptr;
	LIST elem1,elem2;
	FUNC f;
	LIST_LOOP(elem1,(LIST)I_GET(body)) {
	  ivars=L_EMPTY; ovars=L_EMPTY;
	  cl_ioterms(l_push(lit=L_GET(elem1),unit),ivars,
		ovars,(ITEM)NULL,FALSE,FALSE,TRUE);
	  i_dec(l_pop(unit));
	  if (L_EMPTYQ(set_int(both=l_copy(ivars),ovars))) {
	   LIST_LOOP(elem2,(LIST)I_GET(ovars)) {
		/* ovars computed from ivars */
	    if (!(*(entry=h_ins(L_GET(elem2),hfmap))))
	      *entry=L_EMPTY;
	    l_push(lvpair=i_tup2(lit,ivars),*entry);
	    i_delete(lvpair);
	   }
	  }
	  i_deletes(both,ivars,ovars,(ITEM)I_TERM);
	}
	f=(FUNC)I_GET(hfmap);
	FUNC_LOOP(fptr,f) /* Reverse lists in hash table */
	  if(*fptr) LIST_LOOP(elem1,(LIST)I_GET(*fptr))
	    l_reverse(F_ELEM(1,L_GET(elem1)));
	i_delete(unit);
	return(hfmap);
}

/*
 * cl_norep/1 - removes all but the first occurrence of a
 *	literal in a clause
 */

ITEM
cl_norep(clause)
	ITEM clause;
	{
	ITEM hseen=h_create(4l),result,*entry,lit;
	register LIST elem,*last=L_LAST(result=L_EMPTY);
	LIST_LOOP(elem,(LIST)I_GET(clause)) {
	  if (!(*(entry=h_ins(lit=L_GET(elem),hseen)))) {
	    *entry=i_inc(lit);
	    last=l_end(i_inc(lit),last);
	  }
	}
	i_delete(hseen);
	return(result);
}

/*
 * cl_rreduce - relational clause reduction
 *	Given clause H<-B, set of negatives Ns, and essential literals
 *	B' = EmptyList.
	UNTIL L seen twice
	  find first literal L st. B = B1/\L/\B2, and
	  H<-B'/\B1/\L covers no elements of N.
	  Let B3 be the set of support literals for L from B1.
		(i.e. they compute any variables in vars(L) - vars(H))
	  Let B = B1 and B' = B3/\L/\B'
	REPEAT
	RETURN(B')
 */

ITEM cl_siglit(),cl_support();

ITEM
cl_rreduce(head,body,essen0,nvars,hfmap,bnegs1)
	ITEM head,body,essen0,hfmap;
	LONG nvars;
	{
	ITEM essentials=l_copy(essen0),body0=l_copy(body),head1,body1,hdvars,
		hseen=h_create(4l),*entry,lit,bnsample=b_sample(smlim,bnegs1),
		support,result;
	register LIST elem;
	PREDICATE seen=FALSE,ndeterm=b_memq((LONG)I_GET(F_ELEM(0l,head)),
		nondeterm);
	LONG literal=1l;
	LIST_LOOP(elem,(LIST)I_GET(essen0))
	    if(!(*(entry=h_ins(lit=L_GET(elem),hseen)))) *entry=i_inc(lit);
	hdvars=ct_terms(head,TRUE,TRUE);
	l_append(body1=l_copy(essen0),body0);
	do {
	    ITEM body2; LIST *last2;
	    if (!(lit=cl_siglit(head,body1,nvars,
		last2=L_LAST(body2=L_EMPTY),bnsample)))
		{i_delete(body2); break;}
	    if(!(*(entry=h_ins(lit,hseen)))) {
		*entry=i_inc(lit);
		i_delete(body1);
		support=cl_support(lit,hdvars,hfmap,hseen,ndeterm);
		body1=l_append(l_copy(support),l_push(lit,body2));
		l_append(support,l_push(lit,essentials));
		i_deletes(body2,essentials,(ITEM)I_TERM);
		essentials=support;
	    }
	    else {seen=TRUE; i_delete(body2);}
	    i_dec(lit);
	} while(!seen);
	result=cl_norep(l_push(head,essentials));
	i_deletes(essentials,body0,body1,hseen,bnsample,hdvars,(ITEM)I_TERM);
	return(result);
}

/*
 * cl_siglit - similar to cl_subduce except that clause is not
 *	necessarily well-ordered and siglit finds the significant
 *	literal which is the first in the body which fails all
 *	negative examples. If no negative examples unify with the
 *	head then it returns NULL.  The lack of well-orderedness means
 *	that backtracking must be taken care of.
 */

#ifdef SUNCHECK
ITEM ct_subduce(),ct_subduces(),ct_getas();
#else
extern ITEM ct_subduce(),ct_subduces(),ct_getas();
#endif

ITEM
cl_siglit(head,body,nvars,last,bnsample)
	ITEM head,body,bnsample;
	register LIST *last;
	LONG nvars;
	{
	ITEM sub0,subs,subs1,lit,oldsubs,newbs;
	LIST elem1;
	PREDICATE found=FALSE;
	if (L_EMPTYQ(subs=ct_subduce(head,sub0=i_create('f',(POINTER)f_zero(
		f_create(nvars+2))),bnsample)))
	  lit=(ITEM)NULL;
	else {
	  LIST_LOOP(elem1,(LIST)I_GET(body)) {
	    subs1=ct_subduces(lit=L_GET(elem1),subs,bbacks);
	    i_delete(subs);
	    subs=subs1;
	    if(L_EMPTYQ(subs)) {
		found=TRUE;
		break;
	    }
	    else last=l_end(i_inc(lit),last);
	  }
	  if(!found) d_error("cl_siglit - literal not found");
	}
	i_deletes(sub0,subs,(ITEM)I_TERM);
	return(i_inc(lit));
}

/* cl_ureduce - universal reduction
 *	Given clause C and negatives Ns.
 * 	Let cred(C) = H<-B'
 *	Let fred(H<-B') = Bs
 *	Cs'' = 0
 *	For Each B In Bs Cs'' += rred(C,B,Ns)
 *	Return(Cs'')
 *
 *	Note that rred is achieved by prefixing body(C) with
 *	B, setting essentials to B and adding each element
 *	of B to "hseen".
 */

ITEM
cl_ureduce(clause)
	ITEM clause;
	{
	LONG nvars=cl_vmax(clause);
	ITEM clause0=l_copy(clause),hfmap=h_create(4l),
		clause1=cl_creduce(clause0),
		head0=l_pop(clause0),
		head1=l_pop(clause1),bnegs1,
		bodies2=cl_freduce(head1,clause1), result, negcov;
	register LIST elem,*last=L_LAST(result=L_EMPTY);
	cl_fmap(clause0,hfmap);
	negcov=cl_subduce(clause,bnegs,smlim);
	ct_rempos(negcov,bnegs1=b_copy(bnegs));
	LIST_LOOP(elem,(LIST)I_GET(bodies2))
	  last=l_end(cl_rreduce(head0,clause0,L_GET(elem),nvars,hfmap,bnegs1),last);
	i_deletes(bnegs1,negcov,clause0,clause1,head0,head1,
		bodies2,hfmap,(ITEM)I_TERM);
	return(result);
}

/*
 * cl_support/5 - finds a sequence of literals which compute the
 *	input variables of the given variable from the variables
 *	in the head of the clause.
 */

ITEM
cl_support(lit,vars,hfmap,hseen,ndeterm)
	ITEM lit,vars,hfmap,hseen;
	PREDICATE ndeterm;
	{
	ITEM unit,ivars,ovars,result=L_EMPTY,hvis,
		*entry,lit1,used,hused=h_create(4l);
	LIST elem;
	cl_ioterms(unit=l_push(lit,L_EMPTY),ivars=L_EMPTY,
		ovars=L_EMPTY, (ITEM)NULL,FALSE,FALSE,TRUE);
	LIST_LOOP(elem,(LIST)I_GET(set_sub(ivars,vars))) {
	    if (used=cl_compset(L_GET(elem),vars,	
		(ITEM)NULL,hfmap,hvis=h_create(4l),hused)) {
	      l_append(result,l_reverse(used));
	      i_deletes(used,hvis,(ITEM)I_TERM);
	    }
	    else {
	      if(debug && !ndeterm) {
		printf("[WARNING, may have insufficient mode declarations for ");
	        i_fwrite(ttyout,lit); printf("]\n");
	      }
	      i_delete(hvis);
	    }
	}
	LIST_LOOP(elem,(LIST)I_GET(result))
	    if(!(*(entry=h_ins(lit1=L_GET(elem),hseen)))) *entry=i_inc(lit1);
	i_deletes(unit,ivars,ovars,hused,(ITEM)I_TERM);
	return(result);
}
