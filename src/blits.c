/* ####################################################################### */

/*                      GOLEM relative lgg construction Routines	   */
/*                      ---------------------------------------		   */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/*
 * ct_blits/1 - constructs n-depth relative lgg of given atoms. This
 *	is done iteratively to depth n by adding in all determinate
 *	literals connected by at least one variable at each level.
 *	The level is set globally as vlim. Typically vlim should
 *	be at most 3 to avoid explosion in number of literals.
 *	The flag 'determ' states whether predicate should be
 *	treated as determinate or not.
 */

ITEM ct_dblits1(),ct_nblits(),ct_dblits();

ITEM
ct_blits(ctlist)
	ITEM ctlist;
	{
	PREDICATE grnd;
	ITEM htab=h_create(6l),lgg,lgterms,iterms=L_EMPTY,
		oterms=L_EMPTY,hterms=h_create(4l),
		ctclause=L_EMPTY,result,allits,
		bs,psym=F_ELEM(0l,HOF((LIST)I_GET(ctlist))),
		*entry1,*entry2,rpatch,pbs,rbs;
	register ITEM elem;
	LIST *last=L_LAST(rpatch=L_EMPTY);
	PREDICATE ndeterm=b_memq((LONG)I_GET(psym),nondeterm);
	LONG ano,atsize,start;
/*
	(LONG)I_GET(varno)=0l;
*/
	I_ASSIGN(varno,0);
	if(*(entry1=h_ins(psym,determs))) { /* determination constraints */
	    bs=B_EMPTY;
	    LIST_DO(elem,*entry1)
		if(*(entry2=f_ins((LONG)I_GET(elem),predatoms)))
		    b_uni(bs,*entry2);
	    LIST_END
	    b_int(bs,bbacks);
	}
	else bs=b_copy(bbacks);
	if(!(*(entry1=f_ins((LONG)I_GET(psym),predatoms))))
	  d_error("ct_blits - predatoms entry missing");
	else pbs=b_int(b_copy(*entry1),bs);
	LIST_DO(elem,ctlist) /* Construct recursive patch */
	    atsize=Y_ELEM(TNO(elem->extra),asz);
	    last=l_end(rbs=b_copy(bs),last); ano=0l;
	    BIT_DO(ano,pbs)  /* Remove any large atoms from self-recursion */
	      if(atsize<=Y_ELEM(ano,asz))
		b_rem(ano,rbs);
	    BIT_END
	LIST_END
	lgg=ct_nlgg(ctlist,htab,&grnd);
	lgterms=ct_terms(lgg,FALSE,TRUE);
	cl_ioterms(l_push(lgg,ctclause),iterms,
		oterms,hterms,FALSE,TRUE,FALSE);
	allits=l_push(lgg,L_EMPTY);
	if(ndeterm) result=ct_nblits(vlim,iterms,oterms,hterms,htab,allits,rpatch,ctlist);
	else result=ct_dblits(vlim,iterms,oterms,hterms,htab,allits,rpatch);
	l_push(lgg,result),
	i_deletes(bs,htab,lgg,lgterms,ctclause,allits,(ITEM)I_TERM);
	i_deletes(iterms,oterms,hterms,rpatch,pbs,(ITEM)I_TERM);
	return(result);
}

/*
 * ct_dblits - construct determinate body literals
 */

ITEM
ct_dblits(i,iterms,oterms,hterms,htab,allits,rpatch)
	LONG i;
	ITEM iterms,oterms,hterms,htab,allits,rpatch;
	{
	LONG nex=1l;
	ITEM result=L_EMPTY,extras;
	while(nex && i-- > 0l) {
	  extras=ct_dblits1(iterms,oterms,htab,rpatch);
	  set_sub(extras,allits);
	  set_uni(allits,extras);
	  l_append(result,extras);
	  nex=l_length(extras);
	  cl_ioterms(allits,iterms,oterms,hterms,TRUE,TRUE,FALSE);
	  i_delete(extras);
	}
	return(result);
}

LIST *dt_cross(),*ct_apatches1(),*ndt_patches();
ITEM ct_tpatches(),ptc_null(),ct_propnd(),nd_getbtpatches(),ct_firstterms();

/*
 * ct_nblits - construct non-determinate body literals
 */

ITEM cl_reorder();

ITEM
ct_nblits(i,iterms,oterms,hterms,htab,allits,rpatch,examples)
	LONG i;
	ITEM iterms,oterms,hterms,htab,allits,rpatch,examples;
	{
	PREDICATE grnd;
	LONG cnt;
	ITEM result,terms=set_uni(l_copy(iterms),oterms),clause,
		tpatches=ct_tpatches(terms,htab),tpatch,vars,oterms1,
		apatch,apatches,finalpatches=L_EMPTY,newpatches,
		btpatches1,apatches1,btpatches2,ttups2,
		ttup,apatches2,inv1,unit,clause1,as;
	/* */ ITEM head=HOF((LIST)I_GET(allits));
	register LIST *last=L_LAST(apatches=L_EMPTY);
	LIST_DO(tpatch,tpatches)
	    last=ct_apatches1(tpatch,rpatch,IN,last);
	LIST_END
	i_sort(ptc_null(apatches));
	apatches1=l_copy(apatches);
	btpatches1=ct_propnd(i,apatches,htab,allits,rpatch);
	inv1=ptc_inverse(btpatches1,TRUE);
	for(cnt=1;cnt<=i;cnt++) {
	    dt_cross(apatches1,TRUE,L_LAST(newpatches=L_EMPTY));
	    ptc_reduce(set_uni(set_uni(finalpatches,i_sort(newpatches)),apatches1));
	    if(cnt==i) {i_delete(newpatches); break;}
	    btpatches2=nd_getbtpatches(finalpatches);
	    ptc_attenuate(spterms,btpatches2,inv1,btpatches1);
	    ttups2=ct_firstterms(cnt,btpatches2);
	    last=L_LAST(apatches2=L_EMPTY);
	    LIST_DO(ttup,ttups2)
		last=ct_apatches1(ttup,rpatch,IN,last);
	    LIST_END
	    ptc_reduce(set_uni(apatches1,i_sort(ptc_null(apatches2))));
	    i_deletes(newpatches,btpatches2,apatches2,ttups2,(ITEM)I_TERM);
	}
	ct_apatches2(finalpatches);	/* Destructively changes atom bitsets
						    to first atom in the set */
	last=L_LAST(clause=L_EMPTY);
	LIST_DO(apatch,finalpatches)
	    last=l_end(ct_nlgg(apatch,htab,&grnd),last);
	LIST_END
	/* cl_fwrite(ttyout,l_push(head,clause)); printf("\n"); i_dec(l_pop(clause)); */
	vars=cl_vars(clause);
	clause1=ct_dblits(1l,vars,oterms1=L_EMPTY,hterms,htab,allits,rpatch);
	i_delete(vars);
	vars=cl_vars(unit=l_push(head,L_EMPTY));
	result=cl_reorder(clause1,vars);
	if(dostats) {	/* Get extra statistics for new clause */
	    as=b_add(TNO(HOF((LIST)I_GET(examples))->extra),B_EMPTY);
	    i_delete(cl_subduce(l_push(head,result),as,smlim));
	    i_dec(l_pop(result));
	    i_delete(as);
	    dostats=FALSE;
	}
	i_deletes(unit,terms,clause,tpatches,vars,oterms1,clause1,(ITEM)I_TERM);
	i_deletes(apatches,finalpatches,btpatches1,inv1,apatches1,(ITEM)I_TERM);
	return(result);
}

/*
 * ct_propnd - propogate nondeterministic term patches through the
 *	literal classes to depth i
 */


ITEM
ct_propnd(i,apatches,htab,allits,rpatch)
	LONG i;
	ITEM apatches,htab,allits,rpatch;
	{
	LONG cnt;
	PREDICATE grnd;
	ITEM result,finalpatches,newpatches,ndpatches;
	finalpatches=L_EMPTY;
	for(cnt=1;cnt<=i;cnt++) {
	    dt_cross(apatches,TRUE,L_LAST(newpatches=L_EMPTY));
	    set_uni(i_sort(newpatches),apatches);
	    set_uni(finalpatches,i_sort(ptc_reduce(newpatches)));
	    if(cnt==i) {i_delete(newpatches); break;}
	    ndt_patches(newpatches,rpatch,L_LAST(ndpatches=L_EMPTY));
	    ptc_reduce(set_uni(apatches,i_sort(ptc_null(ndpatches))));
	    i_deletes(newpatches,ndpatches,(ITEM)I_TERM);
	}
	result=nd_getbtpatches(finalpatches);
	i_delete(finalpatches);
	return(result);
}

/*
 * ptc_attenuate - destructively changes patches1 so that
 *	whenever p in patches1 and p1,..,pn in patches2, p1,..,pn < p, replace p by p1,..,pn
 */

ptc_attenuate(super,patches1,inv2,patches2)
	ITEM super,patches1,inv2,patches2;
	{
	register LONG e,j,e1;
	ITEM result,allps=b_allones(l_length(patches2)),
		alles=b_allones((LONG)I_GET(F_ELEM(2l,super))),
		patch,bs, replaceone,s1,s2,compbs,replaceall=B_EMPTY;
	LIST *last=L_LAST(result=L_EMPTY),elem;
	LIST_DO(patch,patches1)
	    j=0l; replaceone=b_copy(allps);
	    LIST_DO(bs,patch)
		compbs=b_sub(b_copy(alles),bs); e=0l;
		BIT_DO(e,compbs)
		    if((s1=F_ELEM(e,inv2))&&(s2=F_ELEM(j,s1)))
			b_int(replaceone,s2);
		BIT_END
		j++; i_delete(compbs);
	    LIST_END
	    if(b_emptyq(replaceone))
		last=l_end(i_inc(patch),last);
	    else b_uni(replaceall,replaceone);
	    i_delete(replaceone);
	LIST_END
	elem=(LIST)I_GET(patches2); e=e1=0l;
	BIT_DO(e,replaceall)
	    for(;e1!=e;elem=elem->next,e1++);
	    last=l_end(i_inc(L_GET(elem)),last);
	BIT_END
	i_swap(result,patches1);
	i_deletes(allps,alles,replaceall,result,(ITEM)I_TERM);
}

/*
 * ct_firstterms - returns a term tuple by taking the first term
 *	in each bitset in each term patch.
 */

ITEM
ct_firstterms(i,btpatches)
	LONG i;
	ITEM btpatches;
	{
	ITEM patch,tset,result,ttup;
	LIST *last1=L_LAST(result=L_EMPTY),*last2;
	LIST_DO(patch,btpatches)
	    last2=L_LAST(ttup=L_EMPTY);
	    LIST_DO(tset,patch)
		last2=l_end(b_elem(b_first(tset),spterms),last2);
	    LIST_END
	    last1=l_end(ttup,last1);
	LIST_END
	return(result);
}

/*
 * nd_getbtpatches - applies nlgg to each atom patch to find the set
 *	of new term patches. These are returned as bitset term patches.
 */

ITEM ct_nnlgg(),ptc_btoa(),ptc_ttob();
LIST *ct_terms1();

ITEM
nd_getbtpatches(abpatches)
	ITEM abpatches;
	{
	ITEM abpatch,htup=h_create(6),*entry,lgg,vars,apatch,
		result,var;
	register LIST *last=L_LAST(result=L_EMPTY),*lastv;
	PREDICATE grnd;
	LIST_DO(abpatch,abpatches)
	    lgg=ct_nnlgg(apatch=ptc_btoa(abpatch),htup,&grnd);
	    ct_terms1(lgg,lastv=L_LAST(vars=L_EMPTY),TRUE,TRUE);
	    LIST_DO(var,vars)
		if(!(*(entry=h_ins(var,htup))))
		    d_error("nd_getbtpatches - bad variable");
		last=l_end(ptc_ttob(*entry),last);
	    LIST_END
	    i_deletes(lgg,apatch,vars,(ITEM)I_TERM);
	LIST_END
	i_delete(htup);
	return(i_sort(result));
}

/*
 * ct_nlgg/1 - the Reynolds/Plotkin lgg of n terms. Recurses through all
 *	terms simultaneously, mapping term ntuples to unique
 *	variables.
 */

ITEM ct_nmatches();
ITEM ct_newvar();

ITEM
ct_nlgg(terms,htup,grnd)
	ITEM terms,htup;
	PREDICATE *grnd;
	{
	LONG pno=NGRND,tno=NGRND;
	ITEM first,result,*entry;
	if ((first=ct_nmatches(terms)) != (ITEM)NULL) switch(first->item_type) {
	    case 'f': {
		    register FUNC f,f1=(FUNC)I_GET(first);
		    register ITEM *fp,fname1=FNAME(f1);
		    LONG size1=f1->arr_size;
		    register LONG argno=1;
		    PREDICATE subgrnd=TRUE;
		    result=i_create('f',f=f_create(size1));
		    pno=PNO(first->extra);
		    FNAME(f)=i_inc(fname1);
		    ARG_LOOP(fp,f) {
			ITEM arglist=i_create('l',(POINTER)NULL);
			register LIST elem,*last=L_LAST(arglist);
			LIST_LOOP(elem,(LIST)I_GET(terms)) {
			    f1=(FUNC)I_GET(L_GET(elem));
			    last=l_end(i_inc(f1->arr[argno]),last);
			}
			*fp=ct_nlgg(arglist,htup,&subgrnd);
			i_delete(arglist);
			argno++;
		    }
		    if(subgrnd&&pno!=NGRND) tno=TNO(first->extra);
		    else *grnd=FALSE;
		}
		break;
	    case 'v':
		*grnd=FALSE;
	        pno=PNO(first->extra);
		result=i_inc(first);
		break;
	    case 'h': case 'i': case 'r':
	        pno=PNO(first->extra);
	        tno=TNO(first->extra);
		result=i_inc(first);
		break;
	    default:
		d_error("ct_nlgg - bad term type");
	}
	else {
	    ITEM *var=h_ins(terms,htup);
	    *grnd=FALSE;
	    pno=PNO(HOF((LIST)I_GET(terms))->extra);
	    if (!(*var)) *var=ct_newvar();
	    result=i_create('v',(POINTER)I_GET(*var));
	}
	i_delete(first);
	if (!(*(entry=h_ins(result,htup))))
	    *entry=i_inc(terms); /* Two-way mapping */
	result->extra= PT(pno,tno);
	return(result);
}

/*
 * ct_nmatches/1 - subsidiary of ct_nlgg. Tests whether
 *	the function symbols/variable matches.
 */

ITEM
ct_nmatches(terms)
	ITEM terms;
	{
	register LIST elem,termsl=(LIST)I_GET(terms);
	ITEM result=i_inc(HOF(termsl));
	register char ttype=result->item_type;
	PREDICATE different=FALSE;
	FUNC f;
	if (ttype == 'f') f=(FUNC)I_GET(result);
	LIST_LOOP(elem,TOF(termsl)) {
	    ITEM trm=L_GET(elem);
	    char ttype1=trm->item_type;
	    if (ttype != ttype1) different=TRUE;
	    else switch(trm->item_type) {
		case 'f': {
		    FUNC f1=(FUNC)I_GET(trm);
		    if (!ITMEQ(FNAME(f),FNAME(f1)))
			different=TRUE;
		    }
		    break;
		case 'v': case 'h': case 'i': case 'r':
		    if (!ITMEQ(result,trm)) different=TRUE;
		    break;
		default:
		    d_error("ct_nmatches - bad term type");
	    }
	    if (different) break;
	}
	if (different) {
	    i_delete(result);
	    result=(ITEM)NULL;
	}
	return(result);
}

ITEM
ct_newvar()
	{
	
/*

	return(i_create('v',(POINTER)(((LONG)I_GET(varno))++)));
*/
	return(i_create('v',(POINTER)(I_NINC1(varno))));
}

/*
 * ct_dblits1 - find the set of all body nlgg literals formed from the
 *	background atoms which share at least 1 variable with the
 *	given variables.
 */

ITEM ct_apatches();

ITEM
ct_dblits1(ivars,ovars,htup,rpatch)
	ITEM ivars,ovars,htup,rpatch;
	{
	PREDICATE grnd;
	ITEM itpatches,otpatches,apatches,result;
	register ITEM apatch;
	register LIST *last=L_LAST(result=L_EMPTY);
	itpatches=ct_tpatches(ivars,htup);
	otpatches=ct_tpatches(ovars,htup);
	apatches=ct_apatches(itpatches,otpatches,rpatch);
	LIST_DO(apatch,apatches)
	    last=l_end(ct_nlgg(apatch,htup,&grnd),last);
	LIST_END
	i_deletes(itpatches,otpatches,apatches,(ITEM)I_TERM);
	return(i_sort(result));
}

/*
 * ct_tpatches/2 - returns the set of term tuples represented by
 *	the variables. This is done by looking up the hash-table htup.
 */

ITEM
ct_tpatches(vars,htup)
	ITEM vars,htup;
	{
	register ITEM var,result;
	register LIST *last=L_LAST(result=L_EMPTY);
	LIST_DO(var,vars)
	    last=l_end(i_inc(*h_ins(var,htup)),last);
	LIST_END
	return(result);
}

/*
 * ct_terms - finds the set of all sub-terms in a given term. Flags
 *	are passed for VARIABLES_ONLY and ATOM.
 */

ITEM
ct_terms(term,varsonly,atom)
	ITEM term;
	PREDICATE varsonly,atom;
	{
	ITEM result=i_create('l',(POINTER)NULL);
	LIST *last=(LIST *)&(I_GET(result));
	ct_terms1(term,last,varsonly,atom);
	return(i_sort(result));
}

LIST *
ct_terms1(term,last,varsonly,atom)
	ITEM term;
	register LIST *last;
	PREDICATE varsonly,atom;
	{
	switch(term->item_type) {
	    case 'f': {
		FUNC f=(FUNC)I_GET(term);
		register ITEM *fptr;
		ARG_LOOP(fptr,f) last=ct_terms1(*fptr,last,varsonly,FALSE);
		}
		break;
	    case 'v':
		if (varsonly) last=l_end(i_inc(term),last);
		break;
	    case 'h': case 'i': case 'r':
		break;
	    default:
		d_error("ct_terms1 - bad term type");
	}
	if (!varsonly && !atom) last=l_end(i_inc(term),last);
	return(last);
}

ITEM
cl_vars(cl)
	ITEM cl;
	{
	register ITEM result=L_EMPTY,literal;
	register LIST *last=(LIST *)&(I_GET(result));
	LIST_DO(literal,cl)
	    last=ct_terms1(literal,last,TRUE,TRUE);
	LIST_END
	return(i_sort(result));
}

/*
 * ct_apatches - return the set of all atom patches, which when the
 *	lgg is taken will contain at least one of the variables
 *	associated with the given term-tuples.
 */

LIST *ct_determ();

ITEM
ct_apatches(itpatches,otpatches,rpatch)
	ITEM itpatches,otpatches,rpatch;
	{
	register ITEM tpatch;
	ITEM apatches,apatches1;
	register LIST *last=L_LAST(apatches=L_EMPTY),
		*last1=L_LAST(apatches1=L_EMPTY);
	LONG nlits;
	LIST_DO(tpatch,itpatches)
	    last1=ct_apatches1(tpatch,rpatch,IN,last1);
	LIST_END
	LIST_DO(tpatch,otpatches)
	    last1=ct_apatches1(tpatch,rpatch,OUT,last1);
	LIST_END
	last=ct_determ(apatches1,last);
			/* filter out determinate and null patches */
	last=dt_cross(apatches1,FALSE,last);
			/* add in determinate literals that share more
			   than 2 variables, filtering out unused patches. */
	ct_apatches2(apatches);	/* Destructively changes atom bitsets
					to first atom in the set */
	i_delete(apatches1);
	return(i_sort(apatches));
}

/*
 * ct_apatches1/3 - generates tuple of atom sets from terms
 */

LIST *
ct_apatches1(terms,rpatch,mode,last)
	ITEM terms,rpatch;
	LONG mode;
	LIST *last;
	{
	register LONG pathn,*pt;
	ITEM result,*entry,paths,apatch,pio,bas1;
	register LIST tuple=(LIST)I_GET(terms),elem1,elem2;
	if (!(*(entry=f_ins(TNO(HOF(tuple)->extra),tps))))
	    *entry=B_EMPTY;
	paths=b_copy(*entry);
	LIST_LOOP(elem1,TOF(tuple)) {
	    if (!(*(entry=f_ins(TNO(L_GET(elem1)->extra),tps))))
		*entry=B_EMPTY;
	    b_int(paths,*entry);
	}
	pathn=0l;
	BIT_DO(pathn,paths)
	    LIST *last1;
	    if ((pio=F_ELEM(pathn,pathio)) &&
		mode && (int)I_GET(pio)!=mode) continue;
	    /* Skip paths which have wrong mode */
	    last=l_end(apatch=L_EMPTY,last);
	    last1=L_LAST(apatch);
	    LIST_LOOP2(elem1,elem2,tuple,(LIST)I_GET(rpatch)) {
		FNDPT(pathn,TNO(L_GET(elem1)->extra),pt);
		last1=l_end(bas1=b_int(b_copy(F_ELEM(GETPT(pt),ptas)),L_GET(elem2)),last1);
	    }
	BIT_END
	i_delete(paths);
	return(last);
}

/*
 * ct_apatches2(apatches) - destructively changes atom bitsets
 *	to first atom in the set
 */

int
ct_apatches2(apatches)
	ITEM apatches;
	{
	register LIST elem1,elem2;
	LIST_LOOP(elem1,(LIST)I_GET(apatches)) {
	  LIST_LOOP(elem2,(LIST)I_GET(L_GET(elem1))) {
	    ITEM aset,atom=b_elem(b_first(aset=L_GET(elem2)),spatoms);
	    i_delete(aset);
	    L_GET(elem2)=atom;
	  }
	}
}

/*
 * ct_determ/2 - filters out the determinate and null patches. These
 *	correspond to the null and unit classes.
 */

LIST *
ct_determ(apatches,last)
	ITEM apatches;
	register LIST *last;
	{
	register LIST *elem1,elem2;
	register ITEM elem;
	register LONG lsofar=0,extra,bsize;
	for(elem1=(LIST *)&I_GET(apatches);*elem1;) {
	    ITEM apatch=L_GET(*elem1);
	    PREDICATE allones=TRUE,null=FALSE;
	    LIST_DO(elem,apatch)
		if ((bsize=b_size(elem))!=1) {
		    allones=FALSE;
		    if(bsize==0) null=TRUE;
		}
	    LIST_END
	    if (allones) { /* determinate literal */
		*last= *elem1; /* remove element and add to
				  output list */
		*elem1= (*elem1)->next;
		last= &((*last)->next);
		*last= (LIST)NULL;
	    }
	    else if (null) { /* null patch */
		elem2= *elem1;
		*elem1= (*elem1)->next;
		i_delete(L_GET(elem2));
		L_DEL(elem2,"ct_determ");
	    }
	    else elem1= &((*elem1)->next);
	}
	return(last);
}


/*
 * ndt_patches/2 - construct non-determinate patches from remainder
 */

ITEM ndt_places();
LIST *ndt_patches1();

LIST *
ndt_patches(abpatches1,rpatch,last)
	ITEM abpatches1,rpatch;
	register LIST *last;
	{
	ITEM htup=h_create(6),*entry,lgg,vars,apatch,places,tbpatch;
	register ITEM abpatch,var;
	register LIST *lastv;
	PREDICATE grnd;
	LIST_DO(abpatch,abpatches1)
	    lgg=ct_nnlgg(apatch=ptc_btoa(abpatch),htup,&grnd);
	    ct_terms1(lgg,lastv=L_LAST(vars=L_EMPTY),TRUE,TRUE);
	    LIST_DO(var,vars)
		if(!(*(entry=h_ins(var,htup))))
		    d_error("ndt_patches - bad variable");
		places=ndt_places(tbpatch=ptc_ttob(*entry));
		last=ndt_patches1(tbpatch,places,rpatch,last);
		i_deletes(places,tbpatch,(ITEM)I_TERM);
	    LIST_END
	    i_deletes(vars,lgg,apatch,(ITEM)I_TERM);
	LIST_END
	i_delete(htup);
	return(last);
}

/*
 * ndt_places/1 - given <T1,..,Tm> return /\ (\/places(tk))
 *					  Tj  tk in Tj
 */

ITEM
ndt_places(tpatch)
	ITEM tpatch;
	{
	register ITEM result=(ITEM)NULL,elem,*sarr,upl;
	PREDICATE first=TRUE;
	LIST_DO(elem,tpatch)
	    sarr=((FUNC)I_GET(tps))->arr; upl=B_EMPTY;
	    BIT_DO(sarr,elem)
		b_uni(upl,*sarr);
	    BIT_END
	    if(first) {result=upl; first=FALSE;}
	    else {b_int(result,upl); i_delete(upl);}
	LIST_END
	return(result);
}

/*
 * ndt_patches1/3 - given V*=tpatch=<T1,..,Tm> and Places(V*)
 *	return {\/atoms(p,t1),..,\/atoms(p,tm):p in Places(V*)}
 *	    t1 in terms(p)/\T1  tm in terms(p)/\Tm
 */

LIST *
ndt_patches1(tpatch,places,rpatch,last)
	ITEM tpatch,places,rpatch;
	register LIST *last;
	{
	register LIST elem1,elem2;
	register LONG place=0l;
	BIT_DO(place,places)
	    ITEM apatch,termsp=F_ELEM(place,pts);
	    LIST *lasta=L_LAST(apatch=L_EMPTY);
	    LIST_LOOP2(elem1,elem2,(LIST)I_GET(tpatch),(LIST)I_GET(rpatch)) {
	      {
		register LONG term=0l,*pt;
		register ITEM terms=b_int(b_copy(L_GET(elem1)),termsp),
			    batoms=B_EMPTY,bs=L_GET(elem2);
		BIT_DO(term,terms)
		    FNDPT(place,term,pt);
		    b_int(b_uni(batoms,F_ELEM(GETPT(pt),ptas)),bs);
		BIT_END
		lasta=l_end(batoms,lasta);
		i_delete(terms);
	      }
	    }
	    last=l_end(apatch,last);
	BIT_END
	return(last);
}

int
ct_showsss(asetssss)
	ITEM asetssss;
	{
	ITEM atom,clause=L_EMPTY;
	LIST elem1,elem2,elem3,elem4,elem5;
	printf("(\n");
	LIST_LOOP(elem1,(LIST)I_GET(asetssss)) {
	  printf("  (\n");
	  LIST_LOOP(elem2,(LIST)I_GET(L_GET(elem1))) {
	    printf("    (\n");
	    LIST_LOOP(elem3,(LIST)I_GET(L_GET(elem2))) {
	      printf("      (\n");
	      LIST_LOOP(elem4,(LIST)I_GET(L_GET(elem3))) {
	       printf("        (\n");
	       LIST_LOOP(elem5,(LIST)I_GET(L_GET(elem4))) {
		printf("          ");
		cl_fwrite(ttyout,l_push(L_GET(elem5),clause));
		i_fnl(ttyout);
		i_delete(l_pop(clause));
	       }
	       printf("        )\n");
	      }
	      printf("      )\n");
	    }
	    printf("    )\n");
	  }
	  printf("  )\n");
	}
	printf(")\n");
	i_delete(clause);
}

/*
 * ct_nnlgg/1 - modified Reynolds/Plotkin lgg of n term-sets. Recurses through all
 *	terms simultaneously, mapping term ntuples to unique
 *	variables. Variables represented by tuples of term-sets
 *	to allow for convenient representation of existential variables.
 */

ITEM ct_nnmatches();

ITEM
ct_nnlgg(tpatch,htup,grnd)
	ITEM tpatch,htup;
	PREDICATE *grnd;
	{
	LONG pno=NGRND,tno=NGRND;
	ITEM first,result,*entry;
	if ((first=ct_nnmatches(tpatch)) != (ITEM)NULL) switch(first->item_type) {
	    case 'f': {
		    register FUNC f,f1=(FUNC)I_GET(first);
		    register ITEM *fp,fname1=FNAME(f1);
		    LONG size1=f1->arr_size;
		    register LONG argno=1;
		    PREDICATE subgrnd=TRUE;
		    result=i_create('f',f=f_create(size1));
		    pno=PNO(first->extra);
		    FNAME(f)=i_inc(fname1);
		    ARG_LOOP(fp,f) {
			ITEM newtpatch;
			register LIST elem1,elem2,*last1=L_LAST(newtpatch=L_EMPTY);
			LIST_LOOP(elem1,(LIST)I_GET(tpatch)) {
			  ITEM newterms;
			  register LIST *last2=L_LAST(newterms=L_EMPTY);
			  LIST_LOOP(elem2,(LIST)I_GET(L_GET(elem1))) {
			    f1=(FUNC)I_GET(L_GET(elem2));
			    last2=l_end(i_inc(f1->arr[argno]),last2);
			  }
			  last1=l_end(i_sort(newterms),last1);
			}
			*fp=ct_nnlgg(newtpatch,htup,&subgrnd);
			i_delete(newtpatch);
			argno++;
		    }
		    if(subgrnd&&pno!=NGRND) tno=TNO(first->extra);
		    else *grnd=FALSE;
		}
		break;
	    case 'v':
		*grnd=FALSE;
	        pno=PNO(first->extra);
		result=i_inc(first);
		break;
	    case 'h': case 'i': case 'r':
	        pno=PNO(first->extra);
	        tno=TNO(first->extra);
		result=i_inc(first);
		break;
	    default:
		d_error("ct_nnlgg - bad term type");
	}
	else {
	    ITEM *var=h_ins(tpatch,htup);
	    *grnd=FALSE;
	    pno=PNO(HOF((LIST)I_GET(HOF((LIST)I_GET(tpatch))))->extra);
	    if (!(*var)) *var=ct_newvar();
	    result=i_create('v',(POINTER)I_GET(*var));
	}
	i_delete(first);
	if (!(*(entry=h_ins(result,htup))))
	    *entry=i_inc(tpatch); /* Two-way mapping */
	result->extra= PT(pno,tno);
	return(result);
}

/*
 * ct_nnmatches/1 - subsidiary of ct_nnlgg. Tests whether
 *	the function symbols/variable matches.
 */

ITEM
ct_nnmatches(tpatch)
	ITEM tpatch;
	{
	register LIST elem1,elem2,termsl=(LIST)I_GET(tpatch);
	ITEM result=i_inc(HOF((LIST)I_GET(HOF(termsl))));
	register char ttype=result->item_type;
	PREDICATE different=FALSE;
	FUNC f;
	if (ttype == 'f') f=(FUNC)I_GET(result);
	LIST_LOOP(elem1,termsl) {
	  LIST_LOOP(elem2,(LIST)I_GET(L_GET(elem1))) {
	    ITEM trm=L_GET(elem2);
	    char ttype1=trm->item_type;
	    if (ttype != ttype1) different=TRUE;
	    else switch(trm->item_type) {
		case 'f': {
		    FUNC f1=(FUNC)I_GET(trm);
		    if (!ITMEQ(FNAME(f),FNAME(f1)))
			different=TRUE;
		    }
		    break;
		case 'v': case 'h': case 'i': case 'r':
		    if (!ITMEQ(result,trm)) different=TRUE;
		    break;
		default:
		    d_error("ct_nnmatches - bad term type");
	    }
	    if (different) break;
	  }
	}
	if (different) {
	    i_delete(result);
	    result=(ITEM)NULL;
	}
	return(result);
}

/*
 * ptc_btoa(abpatch) - translates an atom patch using an atom bitset
 *	to normal atom set representation.
 */

ITEM
ptc_btoa(abpatch)
	ITEM abpatch;
	{
	ITEM result;
	register LIST elem,*last=L_LAST(result=L_EMPTY);
	LIST_LOOP(elem,(LIST)I_GET(abpatch))
	    last=l_end(b_btos(spatoms,L_GET(elem)),last);
	return(result);
}

/*
 * ptc_ttob(tpatch) - translates a term patch using a normal term representation
 *	to term bitset representation.
 */

ITEM
ptc_ttob(tpatch)
	ITEM tpatch;
	{
	ITEM result,bterms;
	register LIST elem1,elem2,*last=L_LAST(result=L_EMPTY);
	LIST_LOOP(elem1,(LIST)I_GET(tpatch)) {
	    last=l_end(bterms=B_EMPTY,last);
	    LIST_LOOP(elem2,(LIST)I_GET(L_GET(elem1)))
		b_add(TNO(L_GET(elem2)->extra),bterms);
	}
	return(result);
}

/*
 * cl_reorder(clause,vars) - re-orders the clause body so that variables
 *	"chain" literals together. Uses substats to get efficient
 *	ordering.
 */

int cl_vlits1();
LONG ct_stat();

#define UNKNOWN 9999l

ITEM
cl_reorder(clause,vars)
	ITEM clause,vars;
	{
	ITEM var,lit,hlits=h_create(5l),result,bvars=B_EMPTY,nlit,nlits,
		best,newvars,vars0=i_sort(l_copy(vars)),*entry;
	LIST *last=L_LAST(nlits=L_EMPTY);
	LONG stat;
	LIST_DO(var,vars)
	    b_add((LONG)I_GET(var),bvars);
	LIST_END
	LIST_DO(lit,clause)
	    stat=ct_stat(lit,bvars);
	    nlit=i_tup2(i_dec(I_INT(stat)),lit);
	    last=l_end(nlit,last);
	    cl_vlits1(nlit,nlit,hlits);
	LIST_END
	i_sort(nlits);
	last=L_LAST(result=L_EMPTY);
	while(!L_EMPTYQ(nlits)) {
	    best=l_pop(nlits);
	    if((LONG)I_GET(F_ELEM(0l,best))>=(UNKNOWN-l_length(vars0)))
		dostats=TRUE;
		/* Take more stats iff literals have unknown no. of matches */
	    last=l_end(i_inc(lit=F_ELEM(1l,best)),last);
	    newvars=ct_terms(lit,TRUE,TRUE);
	    set_sub(newvars,vars0);
	    set_uni(vars0,newvars);
	    LIST_DO(var,newvars)
	        b_add((LONG)I_GET(var),bvars);
	    LIST_END
	    LIST_DO(var,newvars)
		if(!(*(entry=h_ins(var,hlits))))
		    d_error("cl_reorder - missing variable");
		LIST_DO(nlit,*entry)
		  (LONG)I_GET(F_ELEM(0l,nlit))=
			ct_stat(F_ELEM(1l,nlit),bvars);
		LIST_END
	    LIST_END
	    i_sort(nlits);
	    i_deletes(best,newvars,(ITEM)I_TERM);
	}
	i_deletes(hlits,bvars,nlits,vars0,(ITEM)I_TERM);
	return(result);
}

/*
 * ct_stat(lit,bvars) - constructs a set representing the open places
 *	in the literal and uses substats to work out statistics for
 *	the literal.
 */

LIST *ct_stat1();

LONG
ct_stat(lit,bvars)
	ITEM lit,bvars;
	{
	ITEM places,*entry;
	LIST *last=L_LAST(places=L_EMPTY);
	LONG result,nbound=0l;
	ct_stat1(lit,bvars,&nbound,last);
	if(L_EMPTYQ(places)) result=1l;
	else {
	  i_sort(places);
	  if(!(*(entry=h_ins(places,substats)))) result=UNKNOWN-nbound;
	  else result=(LONG)I_GET(*entry);
	}
	i_delete(places);
	return(result);
}

LIST *
ct_stat1(term,bvars,nbound,last)
	ITEM term,bvars;
	LIST *last;
	LONG *nbound;
	{
	switch(term->item_type) {
	    case 'f': {
		FUNC f=(FUNC)I_GET(term);
		ITEM *fptr;
		ARG_LOOP(fptr,f) last=ct_stat1(*fptr,bvars,nbound,last);
	      }
	      break;
	    case 'v': {
	        if(!b_memq((LONG)I_GET(term),bvars))
		    last=l_end(I_INT(PNO(term->extra)),last);
		else (*nbound)++; /* Better to have some bound vars */
	      }
	      break;
	    case 'h': case 'i': case 'r':
	      break;
	    default:
		d_error("cl_stat1 - bad term type");
	}
	return(last);
}

/* cl_reminf(clause) - destructively removes any atom in the tail
 *	of the clause which contains a superset of the variables
 *	in the head of the clause.
 */

ITEM ct_bvars();
LONG ct_acost();

int
cl_reminf(clause,htab)
	ITEM clause,htab;
	{
	LIST *last=L_LAST(clause),elem;
	ITEM head=HOF(*last),bvarshd,bvarsbd,atom;
	LONG phd=(LONG)I_GET(F_ELEM(0l,head)),hdcost;
	ct_bvars(head,bvarshd=B_EMPTY);
	hdcost=ct_acost(head,htab);
	last= &TOF(*last);
	while(*last) {
	  bvarsbd=B_EMPTY;
	  if(phd==(LONG)I_GET(F_ELEM(0l,atom=HOF(elem= *last))) &&
		(b_subseteq(bvarshd,ct_bvars(HOF(*last),bvarsbd))||
		 hdcost<=ct_acost(atom,htab))) {
	    *last= TOF(*last);
	    i_delete(atom);
	    L_DEL(elem,"cl_reminf");
	  }
	  else last= &TOF(*last);
	  i_delete(bvarsbd);
	}
	i_delete(bvarshd);
}

/* ct_bvars(term,bvars) - inserts all variable numbers in term into bvars
 */

ITEM
ct_bvars(term,bvars)
	ITEM term,bvars;
	{
	FUNC f;
	register ITEM *fptr;
	switch(term->item_type) {
	  case 'f':
	    f=(FUNC)I_GET(term);
	    ARG_LOOP(fptr,f) ct_bvars(*fptr,bvars);
	    break;
	  case 'v':
	    b_add((LONG)I_GET(term),bvars);
	    break;
	  case 'i': case 'r': case 'h':
	    break;
	  default:
	  d_error("ct_bvars - bad term type");
	}
	return(bvars);
}

/* ct_acost(atom,htab) - sums the cost of the arguments for all
 *	lgg substitutions of the atom
 */

LONG
ct_acost(atom,htab)
	ITEM atom,htab;
	{
	FUNC f=(FUNC)I_GET(atom);
	ITEM *fptr,*entry;
	LONG result=0l;
	ARG_LOOP(fptr,f) {
	  if(!(*(entry=h_ins(*fptr,htab))))
	    d_error("ct_acost - no entry in hash-table");
	  result+=cl_cost(*entry);
	}
	return(result);
}
