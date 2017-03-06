/* ####################################################################### */

/*                      GOLEM predicate invention routines		   */
/*                      ----------------------------------		   */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/* w_construct(atoms) - takes a set of atoms and constructs
 *	the ij-determinate rlgg. From this the following
 *	variables are extracted
 *	  hiterms - input terms in the head
 *	  iterms - all input variables, in head and derived
 *	  oterms - all output variables, in head and derived
 *	If no negative instances are covered then w_construct
 *	  succeeds with the given cover
 *	A set of substitutions for input and output variables
 *	  for all covered  positive and negative instances are
 *	  constructed
 *	From the substitutions a set of variable subset (vsubsets)
 *	  is constructed representing new predicates. Each of
 *	  these contains a minimal number of variables required
 *	  for a consistent model of the new predicate
 *	Definitions are constructed for each of the new predicates
 *	The predicate producing highest compression is added to
 *	  the clause set, with the appropriate call added to
 *	  the rlgg of the given atoms.
 */

ITEM w_rlgg(),w_vsubsets(),w_vconv(),w_extractas();
int w_assert(),w_generalise(),w_retract();
PREDICATE w_update(),w_newcall();

PREDICATE
w_construct(atoms,pred,bestposcov,bestcomp,test)
	ITEM atoms,pred,*bestposcov;
	LONG *bestcomp;
	PREDICATE test;
	{
	ITEM vsubsets,vsubset,bestvs=(ITEM)NULL,cl,bivars,var,
		bestcs=(ITEM)NULL,vars,head,possubs1,
		negsubs1,clause1,bclash,bcover,clause,
		possubs,negsubs,hivars,ivars,ovars;
	LONG result=FALSE,oldvlim=vlim;
	PREDICATE fail=FALSE;
	clause=w_rlgg(atoms,&hivars,&ivars,&ovars);
	possubs=cl_subduce(clause,bfores,smlim);
	if(L_EMPTYQ(negsubs=cl_subduce(clause,bnegs,smlim))) {
	  if(!(*bestposcov)||l_length(possubs)>b_size(*bestposcov)) {
	    i_delete(*bestposcov);
	    *bestposcov=w_extractas(possubs);
	    result=TRUE;
	  }
	  i_deletes(possubs,clause,negsubs,hivars,ivars,ovars,(ITEM)I_TERM);
	  return(result);
	}
	printf("CONSTRUCT\n"); cl_print(clause); i_print(clause);
	printf("ITERMS: "); i_print(ivars); printf("OTERMS: "); i_print(ovars);
	printf("ATOMS: "); i_print(atoms);
	bivars=B_EMPTY;
	LIST_DO(var,ivars) b_add((LONG)I_GET(var),bivars); LIST_END
	vars=set_uni(l_copy(ivars),ovars);
	head=l_pop(clause);
	vsubsets=w_vsubsets(vars,hivars,ivars,ovars,bivars,possubs,negsubs,clause);
	l_push(i_dec(head),clause);
	printf("RED VARS: "); i_print(vsubsets);
	if(test) vlim=1l;
	LIST_DO(vsubset,vsubsets)
	  i_print(vsubset);
	  if(test) {
	    w_assert(vsubset,possubs,negsubs,bivars,pred,TRUE);
	    if(!w_newcall(vsubset,clause,&clause1,FALSE)) {
	      w_retract();
	      continue;
	    }
	    printf("  Reduced clause "); cl_print(clause1);
	    w_retract();	/* retract new atoms and properties */
	    possubs1=cl_subduce(clause1,bfores,smlim);
	    bcover=(ITEM)NULL;
	    if(test&& *bestposcov &&b_subseteq(bcover=w_extractas(possubs1),*bestposcov)) {
	      i_deletes(clause1,possubs1,bcover,(ITEM)I_TERM);
	      continue;
	    }
	    printf("Calling instances=%d\n",l_length(possubs1));
	    negsubs1=cl_subduce(clause1,bnegs,smlim);
	  }
	  else {
	    possubs1=i_inc(possubs); negsubs1=i_inc(negsubs);
	    bclash=bcover=(ITEM)NULL;
	  }
	  w_assert(vsubset,possubs1,negsubs1,bivars,pred,TRUE);
				     /* assert + store retract properties */
	  if(b_emptyq(bclash=b_int(b_copy(bfores),bnegs)) &&
	      (test||w_newcall(vsubset,clause,&clause1,TRUE))) {
	    printf("Called instances=%d\n",b_size(bfores));
	    w_generalise(test); /* generalises temporary foreground facts */
	    i_sort(l_push(clause1,rules));
	    result=w_update(vsubset,possubs1,bestcomp,&bestvs,&bestcs,bestposcov);
	  }
	  else fail=TRUE;
	  w_retract();	/* retract new atoms and properties */
	  i_deletes(clause1,possubs1,negsubs1,bclash,bcover,(ITEM)I_TERM);
	  if(test && (result||fail)) break;
	LIST_END
	vlim=oldvlim;
	if(bestvs && !test) {	/* add in the best */
	  w_assert(bestvs,possubs,negsubs,bivars,pred,FALSE);
	  i_delete(hypothesis);
	  LIST_DO(cl,bestcs)
	    hypothesis=i_inc(cl);
	    c_addhyp();
	  LIST_END
	}
	i_deletes(vsubsets,bestvs,bestcs,vars,bivars,(ITEM)I_TERM);
	i_deletes(clause,possubs,negsubs,hivars,ivars,ovars,(ITEM)I_TERM);
	return(result);
}

ITEM ct_dblits(), w_vrenum();

/* w_rlgg(atoms,hiterms,iterms,oterms) - take the determinate
 *	rlgg of atoms and return head-input terms, input and
 *	output terms
 */

ITEM
w_rlgg(atoms,hiterms,iterms,oterms)
	ITEM atoms,*hiterms,*iterms,*oterms;
	{
	PREDICATE grnd;
	ITEM htab=h_create(6l),lgg,lgterms,hiterms1,iterms1,
		hterms=h_create(4l),result,oterms1,hvars,
		ctclause=L_EMPTY,clause,allits,
		bs,psym=F_ELEM(0l,HOF((LIST)I_GET(atoms))),
		*entry1,*entry2,rpatch,pbs,rbs;
	register ITEM elem;
	LONG nvars=0l;
	LIST *last=L_LAST(rpatch=L_EMPTY);
	LONG ano,atsize;
	iterms1=L_EMPTY; oterms1=L_EMPTY;
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
	  d_error("w_rlgg - predatoms entry missing");
	else pbs= b_int(b_copy(*entry1),bs);
	LIST_DO(elem,atoms) /* Construct recursive patch */
	    atsize=Y_ELEM(TNO(elem->extra),asz);
	    last=l_end(rbs=b_copy(bs),last); ano=0l;
	    BIT_DO(ano,pbs)  /* Remove any large atoms from self-recursion */
	      if(atsize<=Y_ELEM(ano,asz))
		b_rem(ano,rbs);
	    BIT_END
	LIST_END
	lgg=ct_nlgg(atoms,htab,&grnd);
	lgterms=ct_terms(lgg,FALSE,TRUE);
	cl_ioterms(l_push(lgg,ctclause),iterms1,
		oterms1,hterms,FALSE,TRUE,FALSE);
	hiterms1=l_copy(iterms1);
	allits=l_push(lgg,L_EMPTY);
	clause=ct_dblits(vlim,iterms1,oterms1,hterms,htab,allits,rpatch);
	l_push(lgg,clause);
	/* cl_reminf(clause,htab); */
	result=w_vrenum(clause,&nvars,&hvars);
	*hiterms=i_sort(w_vconv(hiterms1,hvars,TRUE));
	*iterms=i_sort(w_vconv(iterms1,hvars,TRUE));
	*oterms=i_sort(w_vconv(oterms1,hvars,TRUE));
	i_deletes(pbs,bs,htab,lgg,lgterms,ctclause,allits,hvars,(ITEM)I_TERM);
	i_deletes(clause,hterms,rpatch,hiterms1,iterms1,oterms1,(ITEM)I_TERM);
	return(result);
}

ITEM ct_vrenum();

/* w_vrenum(clause,nvars,hvars) - renumbers variables in clause. Returns the
 *	number of variables used (nvars) and a hash-table which translates
 *	from old variables to new.
 */

ITEM
w_vrenum(clause,nvars,hvars)
	ITEM clause,*hvars;
	LONG *nvars;
	{
	ITEM result;
	LIST elem,*last=L_LAST(result=L_EMPTY);
	*hvars=h_create(4l);
	LIST_LOOP(elem,(LIST)I_GET(clause))
	    last=l_end(ct_vrenum(L_GET(elem),nvars,*hvars),last);
	return(result);
}


LIST *w_vectors();
ITEM w_vsubsets1(),w_reduce(),w_order();

/* w_vsubsets - finds a set of reduced variable subsets.
 *	Substitutions are represented in an efficient way
 *	by normalising the term numbering using a vector of
 *	superset structures. This allows substitutions to be
 *	represented using integer arrays created by w_vectors.
 *	Each substitution array is tagged with its sign (pos/neg).
 */

ITEM
w_vsubsets(vars,hivars,ivars,ovars,bivars,possubs,negsubs,body)
	ITEM vars,hivars,ivars,ovars,bivars,possubs,negsubs,body;
	{
	LONG nvars=l_length(vars);
	FUNC f;
	ITEM supers=i_create('f',(POINTER)(f=f_create(nvars))),
		vectors,*fptr,vsubsets1,vsubset1,result,
		vsubset;
	LIST *last=L_LAST(vectors=L_EMPTY);
	FUNC_LOOP(fptr,f)
	  *fptr=i_tup3(i_dec(i_create('f',(FUNC)f_zero(f_create(8l)))),
		i_dec(h_create(4l)),i_dec(I_INT(0l)));
	last=w_vectors(vars,possubs,supers,TRUE,last);
	w_vectors(vars,negsubs,supers,FALSE,last);
	vsubsets1=w_vsubsets1(hivars,ivars,ovars,body);
	last=L_LAST(result=L_EMPTY);
	LIST_DO(vsubset1,vsubsets1)
	  if(vsubset=w_reduce(vectors,vsubset1,supers))
	    last=l_end(w_order(i_sort(vsubset),bivars),last);
	LIST_END
	i_deletes(supers,vectors,vsubsets1,(ITEM)I_TERM);
	return(i_sort(result));
}

/* w_order(vars,bivars) - orders the variables with input variables
 *	first followed by output variables.
 */

ITEM
w_order(vars,bivars)
	ITEM vars,bivars;
	{
	ITEM ivars,ovars,var;
	LIST *lasti=L_LAST(ivars=L_EMPTY),*lasto=L_LAST(ovars=L_EMPTY);
	LIST_DO(var,vars)
	  if(b_memq((LONG)I_GET(var),bivars))
	    lasti=l_end(i_inc(var),lasti);
	  else lasto=l_end(i_inc(var),lasto);
	LIST_END
	l_append(ivars,ovars);
	i_delete(ovars);
	return(ivars);
}

ITEM w_vsubset();

/* w_vsubsets1 - generates various ordered subsets of variables for
 *	reducing the variables in the new predicate.
 *	8 * |head-input-variables| orderings are produced
 *	corresponding to all permutations of
 *	  a) removing each head-input-varibale
 *	  b) removing/not-removing dependents of each
 *		head-input-varibale
 *	  c) reversing the input variables
 *	  d) reversing the output variables
 */

ITEM
w_vsubsets1(hivars,ivars,ovars,body)
	ITEM hivars,ivars,ovars,body;
	{
	ITEM hivar,result,dep;
	LONG cnt;
	LIST *last=L_LAST(result=L_EMPTY);
	LIST_DO(hivar,hivars)
	  for(cnt=1l;cnt>=0;cnt--) {
	    dep=b_add((LONG)I_GET(hivar),B_EMPTY);
	    if(!cnt) w_dependents(hivar,body,dep);
	    last=l_end(w_vsubset(hivar,ivars,l_reverse(ovars),dep),last); /* 01 */
	    last=l_end(w_vsubset(hivar,l_reverse(ivars),ovars,dep),last); /* 11 */
	    last=l_end(w_vsubset(hivar,ivars,l_reverse(ovars),dep),last); /* 10 */
	    last=l_end(w_vsubset(hivar,l_reverse(ivars),ovars,dep),last); /* 00 */
	    i_delete(dep);
	  }
	LIST_END
	return(result);
}

/* w_vsubset(omit,ivars,ovars,dep) - produce a particular
 *	vsubset. omit is used to omit a variable and dep is used
 *	to omit dependencies.
 */

ITEM
w_vsubset(omit,ivars,ovars,dep)
	ITEM omit,ivars,ovars,dep;
	{
	ITEM result,var,*entry;
	LIST *last=L_LAST(result=L_EMPTY);
	LIST_DO(var,ivars)
	  if((I_GET(var) != I_GET(omit)) && !b_memq((LONG)I_GET(var),dep))
	    last=l_end(i_inc(var),last);
	LIST_END
	LIST_DO(var,ovars)
	  if((I_GET(var) != I_GET(omit)) && !b_memq((LONG)I_GET(var),dep))
	    last=l_end(i_inc(var),last);
	LIST_END
	return(result);
}

/* w_dependent(v,body,hvars) - places all functionally dependent
 *	variables of v into hvars using body. Functionally
 *	dependency is decided on the basis that if
 *	vars(atom) = {v,w} for atom in body then w is
 *	functionally dependent on v.
 */

int
w_dependents(v,body,dep)
	ITEM v,body,dep;
	{
	ITEM atom,vars,var,bvars;
	LIST_DO(atom,body)
	  vars=ct_terms(atom,TRUE,TRUE);
	  bvars=B_EMPTY;
	  LIST_DO(var,vars)
	    b_add((LONG)I_GET(var),bvars);
	  LIST_END
	  if(b_size(b_sub(bvars,dep))==1)
	    b_uni(dep,bvars);
	  i_deletes(bvars,vars,(ITEM)I_TERM);
	LIST_END
}

/* w_vectors(vars,subs,supers,pos,last) - returns a set of
 *	integer array vectors based on the superset mappings
 *	of the terms in subs. The extra field is used to
 *	say whether example is positive or negative.
 */

LIST *
w_vectors(vars,subs,supers,pos,last)
	ITEM vars,subs,supers;
	PREDICATE pos;
	LIST *last;
	{
	ITEM var,sub,vector,t;
	LONG vno,tno;
	LIST_DO(sub,subs)
	  last=l_end(vector=Y_EMPTY,last);
	  vector->extra=pos;
	  LIST_DO(var,vars)
	    vno=((LONG)I_GET(var));
	    tno=TNO((F_ELEM(vno+2l,sub))->extra);
	    Y_PUSH(b_num(t=I_INT(tno),F_ELEM(vno,supers)),vector);
	    i_delete(t);
	  LIST_END
	LIST_END
	return(last);
}

/* w_reduce(vectors,vsubset,supers) - returns a reduced vsubset.
 *	Reduction is carried out by finding the first variable
 *	which separates all positive from negative instances.
 *	This is similar to building a decision tree with a fixed
 *	ordering. All subsequent variables are discarded and
 *	the significant variable is placed at the front of the
 *	list. This is iterated until the first variable is reseen.
 *	If the reduced subset is empty or no subset differentiates
 *	positives from negatives then the function returns NULL.
 */

ITEM
w_reduce(vectors,vsubset,supers)
	ITEM vectors,vsubset,supers;
	{
	LONG cnt,max,fseen=I_TERM;
	ITEM vector,end,first,*entry;
	LIST *last;
	PREDICATE seen=FALSE;
	do {
	  max=0l;
	  if(!w_reduce1((LIST)I_GET(vsubset),vectors,supers,1l,&max)||!max)
	    return((ITEM)NULL);
	  cnt=1l;
	  LISTP_LOOP(last,vsubset)
	    if(cnt++ == max) {
	      end=i_create('l',(POINTER)*last);
	      *last=(LIST)NULL;
	      l_push(first=i_dec(l_pop(end)),vsubset);
	      i_delete(end);
	      if(fseen==I_TERM) fseen=(LONG)I_GET(first);
	      else if(fseen==(LONG)I_GET(first)) seen=TRUE;
	      break;
	    }
	} while(!seen);
	return(vsubset);
}

/* w_reduce1(index,vectors,supers,depth,max) -
 *	finds the first variable which separates
 *	all positive from negative instances. This
 *	is done by recursively partitioning the
 *	examples represented by vectors until they
 *	are all positive or all negative. The maximum
 *	depth at which this happens is recorded.
 */

PREDICATE
w_reduce1(index,vectors,supers,depth,max)
	LIST index;
	ITEM vectors,supers;
	LONG depth,*max;
	{
	PREDICATE pos,neg;
	ITEM *entry,vector,*fptr,choice;
	FUNC f;
	LONG i;
	pos=neg=FALSE;
	LIST_DO(vector,vectors)
	  if(vector->extra) pos=TRUE;
	  else neg=TRUE;
	LIST_END
	if(!(pos&&neg)) {
	  if(depth-1 > *max) *max=depth-1;
	  return(TRUE);
	}
	else if(!index) return(FALSE);
	i=(LONG)I_GET(L_GET(index));
	choice=i_create('f',f=f_zero(f_create(
		(LONG)I_GET(F_ELEM(2l,F_ELEM(i,supers))))));
	LIST_DO(vector,vectors)
	  if(!(*(entry=f_ins(Y_ELEM(i,vector),choice))))
	    *entry=L_EMPTY;
	  l_push(vector,*entry);
	LIST_END
	FUNC_LOOP(fptr,f) {
	  if(*fptr)
	    if(!w_reduce1(index->next,*fptr,supers,depth+1,max)) {
		i_delete(choice);
		return(FALSE);
	    }
	}
	i_delete(choice);
	return(TRUE);
}

int w_assert1(),w_saveprops();

/* Retraction information */
ITEM newname,oldbfores,oldbnegs,oldbbacks,oldrules;
LONG oldsymp,oldpathp,oldtermp,oldatomp,oldgensymn,gensymn=0,
	oldptno;

/* w_assert(vsubsets,possubs,negsubs,ivars,retractable) -
 *	constructs a set of ground atoms and integrates them
 *	into the indexed structures for terms, paths etc.
 *	If retractable is true then various global variables
 *	are assigned to allow all these properties to be
 *	retracted. The new predicate is given a gensymed
 *	name of the form pX where X is a natural number.
 *	Modes are declared in accordance with use of
 *	input/output variables.
 */

int
w_assert(vsubset,possubs,negsubs,bivars,pred,retractable)
	ITEM vsubset,possubs,negsubs,bivars,pred;
	PREDICATE retractable;
	{
	char buff[MAXWORD];
	LONG nargs=l_length(vsubset),argno;
	ITEM var,mode,*entry,subpred;
	FUNC f;
	if(retractable) w_saveprops();
	sprintf(buff,"p%d",gensymn++);
	newname=i_create('h',(POINTER)QP_ston(buff,nargs));
	mode=i_create('f',(POINTER)(f=f_create(nargs+1)));
	FNAME(f)=i_inc(newname);
	argno=1l;
	LIST_DO(var,vsubset)
	  if(b_memq(((LONG)I_GET(var)),bivars))
	    F_ELEM(argno++,mode)=i_create('h',(POINTER)pplus);
	  else F_ELEM(argno++,mode)=i_create('h',(POINTER)pminus);
	LIST_END
	cl_mdeclare(mode);
	if(*(entry=h_ins(pred,determs))) { /* Determinations */
	  LIST_DO(subpred,*entry)
	    if((LONG)I_GET(pred)!=(LONG)I_GET(subpred))
	      cl_ddeclare(newname,subpred);
	  LIST_END
	  cl_ddeclare(newname,newname);
	}
	w_assert1(newname,vsubset,possubs,bfores,retractable);
	w_assert1(newname,vsubset,negsubs,bnegs,retractable);
	i_delete(mode);
	if(!retractable) i_delete(newname);
}

int
w_assert1(newname,vsubset,subs,bs,retractable)
	ITEM newname,vsubset,subs,bs;
	PREDICATE retractable;
	{
	ITEM var,atom,sub;
	LONG argno,nargs=l_length(vsubset);
	FUNC f;
	LIST_DO(sub,subs)
	  atom=i_create('f',(POINTER)(f=f_create(nargs+1)));
	  FNAME(f)=i_inc(newname);
	  argno=1l;
	  LIST_DO(var,vsubset)
	    F_ELEM(argno++,atom)=
		i_copy(F_ELEM((LONG)I_GET(var)+2l,sub));
	  LIST_END
	  ct_integrate(atom);
	  b_add(TNO(atom->extra),bs);
	  if(bs==bfores) b_add(TNO(atom->extra),bbacks);
	  i_delete(atom);
	LIST_END
}

/* w_saveprops() - saves enough information to allow indexed
 *	structures to be returned to their original state
 *	when new atoms are retracted.
 */

w_saveprops()
	{
	oldsymp=(LONG)I_GET(F_ELEM(2l,spsyms));   /* Symbol supersets */
	oldpathp=(LONG)I_GET(F_ELEM(2l,sppaths)); /* Path superset */
	oldatomp=(LONG)I_GET(F_ELEM(2l,spatoms)); /* Atom superset */
	oldgensymn=gensymn;	  /* Gen-sym no */
	oldptno=ptno;	   	  /* Highest place/term no. */
	oldbfores=bfores; /* Foreground examples */
	bfores=B_EMPTY;
	oldbnegs=bnegs;   /* Negative examples */
	bnegs=B_EMPTY;
	oldbbacks=b_copy(bbacks); /* Background atoms */
	oldrules=rules;	  /* Rules */
	rules=L_EMPTY;
}

int w_spretract(),w_fretract(),w_ptretract();

/* w_retract() - returns all indexed structures to their original
 *	state
 */

int
w_retract()
	{
	LONG newsymp,newpathp,newatomp,n;
	ITEM boldpaths,bnewpaths,usedterms=B_EMPTY;
	gensymn--;
	newsymp=(LONG)I_GET(F_ELEM(2l,spsyms));   /* Symbol supersets */
	newpathp=(LONG)I_GET(F_ELEM(2l,sppaths)); /* Path superset */
	newatomp=(LONG)I_GET(F_ELEM(2l,spatoms)); /* Atom superset */
	for(n=oldatomp;n<newatomp;n++) w_ptretract(n,usedterms);
	w_spretract(spsyms,oldsymp,newsymp);
	w_spretract(sppaths,oldpathp,newpathp);
	w_spretract(spatoms,oldatomp,newatomp);
	h_del(newname,modes);
	h_del(newname,determs);
	w_fretract(predatoms,oldsymp,newsymp); w_fretract(pts,oldpathp,newpathp);
	w_fretract(pas,oldpathp,newpathp); w_fretract(pathio,oldpathp,newpathp);
	w_fretract(ptas,oldptno,ptno);
	bnewpaths=b_sub(b_allones(newpathp),boldpaths=b_allones(oldpathp));
	n=0l;
	BIT_DO(n,usedterms)
	  b_sub(F_ELEM(n,tps),bnewpaths);
	BIT_END
	ptno=oldptno;
	i_deletes(newname,bfores,bnegs,bbacks,usedterms,
		boldpaths,bnewpaths,rules,(ITEM)I_TERM);
	bfores=oldbfores; bnegs=oldbnegs; bbacks=oldbbacks;
	rules=oldrules;
}

/* w_update - updates the best new predicate
 */

PREDICATE
w_update(vsubset,subs,compression,bestvs,bestcs,bestposcov)
	ITEM vsubset,subs,*bestvs,*bestcs,*bestposcov;
	LONG *compression;
	{
	PREDICATE result=FALSE;
	LONG csdiff;
	ITEM atoms=cl_extractas(subs);
	if((csdiff=(cl_cost(atoms)-cl_costs(rules)))> *compression) {
	  *compression=csdiff;
	  i_deletes(*bestvs,*bestcs,*bestposcov,(ITEM)I_TERM);
	  *bestvs=i_inc(vsubset);
	  *bestcs=i_inc(rules);
	  *bestposcov=w_extractas(subs);
	  result=TRUE;
	}
	printf("  Compression=%d\n",csdiff);
	i_delete(atoms);
	return(result);
}

/* w_generalise() - generalises the positive examples
 *	using the same control structure as w_doall
 */

int
w_generalise(test)
	{
	LONG bestcover=0l,minlc,start,cost;
	ITEM clause,atom,pair,goodEs,clauses,atoms,cover,bcover;
	char mess[MAXMESS];
	LONG ncls=(test?2l:9999l);
	goodEs=b_copy(bfores);
	start=cputime();
	while ((b_size(bfores)>=2) && (pair=ct_bestpr(&bestcover,&goodEs))) {
		if(!test) {
		  i_delete(hypothesis);
		  hypothesis=ct_hyp(pair,bestcover,goodEs);
		}
		g_message("Reducing clause");
		clauses=cl_ureduce(hypothesis);
		i_deletes(pair,hypothesis,(ITEM)I_TERM);
		hypothesis=(ITEM)NULL;
		if (L_EMPTYQ(clauses)) {
		    i_delete(clauses);
		    break;
		}
		/* Choose minimum sized clause */
		minlc=99999l;
		LIST_DO(clause,clauses)
		    if((cost=cl_cost(clause))<minlc) {
		      i_delete(hypothesis);
		      hypothesis=i_inc(clause);
		      minlc=cost;
		    }
		LIST_END
		if(hypothesis) {
		    cl_swrite(mess,hypothesis);
		    g_message("Adding clause %s",mess);
		    c_addhyp();
		    if (debug) c_sizes();
		}
		b_uni(goodEs,bfores);
		bestcover=0l;
		i_delete(clauses);
		if(--ncls <= 0l) break;
	}
	g_message("Induction time %ldms",cputime()-start);
	i_delete(goodEs);
	atoms=b_btos(spatoms,bfores);
	LIST_DO(atom,atoms)
	    l_push(i_dec(l_push(atom,L_EMPTY)),rules);
	LIST_END
	i_sort(rules);
	i_delete(atoms);
}

/* w_newcall(vars,clause,clause1,newcall) - makes up call
 *	to new predicate using vars and newname. With this
 *	new predicate added to the end of it clause is
 *	reduced to clause1. newcall is then constructed
 *	containing all the atoms in clause1 except the new
 *	calling atom.
 */

PREDICATE
w_newcall(vars,clause,clause1,call)
	ITEM vars,clause,*clause1;
	PREDICATE call;
	{
	ITEM calll=l_push(newname,l_copy(vars)),
		calla=f_ltof(calll),unit,clauses,newcall,
		clause2,hatoms,atom,*entry,cvars,vars1;
	LIST *last;
	cl_integrate(unit=l_push(calla,L_EMPTY));
	clause2=l_append(l_copy(clause),unit);
	i_swap(bnegs,oldbnegs);	/* Reduction requires negative examples */
	clauses=cl_ureduce(clause2);
	i_swap(bnegs,oldbnegs);
	if(L_EMPTYQ(clauses)) {
	  i_deletes(calll,calla,unit,clause2,clauses,(ITEM)I_TERM);
	  return(FALSE);
	}
	newcall=l_pop(clauses);
	cvars=cl_vars(newcall);
	if(!set_subset(vars1=i_sort(l_copy(vars)),cvars)) {
	  i_deletes(calll,calla,unit,clause2,clauses,newcall,
		cvars,vars1,(ITEM)I_TERM);
	  return(FALSE);
	}
	if(call) *clause1=newcall;
	else {
	  hatoms=h_create(4l);
	  last=L_LAST(*clause1=L_EMPTY);
	  LIST_DO(atom,newcall)
	    if(!(*(entry=h_ins(atom,hatoms))))
	      *entry=i_inc(atom);
	  LIST_END
	  LIST_DO(atom,clause)
	    if(*(entry=h_ins(atom,hatoms))&&atom!=calla)
	      last=l_end(i_inc(atom),last);
	  LIST_END
	  i_deletes(hatoms,newcall,(ITEM)I_TERM);
	}
	i_deletes(cvars,vars1,calll,calla,unit,clauses,clause2,(ITEM)I_TERM);
	return(TRUE);
}

/* w_ptretract(atomn,usedterms) - recurses through atom structure
 *	to retract all path/term pairs, saving usedterms
 */

int
w_ptretract(atomn,usedterms)
	LONG atomn;
	ITEM usedterms;
	{
	ITEM atom=F_ELEM(atomn,F_ELEM(0l,spatoms)),*fptr;
	FUNC f=(FUNC)I_GET(atom);
	ARG_LOOP(fptr,f)
	  w_ptretract1(*fptr,usedterms);
}

int
w_ptretract1(term,usedterms)
	ITEM term,usedterms;
	{
	LONG tno,ex=term->extra,*ptp=pt_ins(PNO(ex),tno=TNO(ex));
	*ptp=PTTERM;
	b_add(tno,usedterms);
	switch(term->item_type) {
	  case 'f':
	    {
	      FUNC f=(FUNC)I_GET(term);
	      ITEM *fptr;
	      ARG_LOOP(fptr,f)
		w_ptretract1(*fptr,usedterms);
	    }
	    break;
	  case 'h': case 'i': case 'r':
	    break;
	  default:
	  d_error("w_ptretract1 - bad term type");
	}
}

/* w_spretract(super,oldmax,newmax) - returns super-set
 *	to its previous state by deleting all hash-entries
 *	and array entries, oldmax <= entry < newmax
 */

int
w_spretract(super,oldmax,newmax)
	ITEM super;
	LONG oldmax,newmax;
	{
	ITEM *sarr=((FUNC)I_GET(super))->arr,
		arr= *sarr++,htable= *sarr++,smax= *sarr,
		*eold=((FUNC)I_GET(arr))->arr+oldmax,
		*enew=((FUNC)I_GET(arr))->arr+newmax;
	while(--enew >= eold) {
	  h_del(*enew,htable);
	  i_delete(*enew);
	  *enew=(ITEM)NULL;
	}
	(LONG)I_GET(smax)=oldmax;
}

/* w_fretract(arr,oldmax,newmax) - removes all entries
 *	in the array, oldmax <= entry < newmax
 */

int
w_fretract(arr,oldmax,newmax)
	ITEM arr;
	LONG oldmax,newmax;
	{
	ITEM *eold=((FUNC)I_GET(arr))->arr+oldmax,
		*enew=((FUNC)I_GET(arr))->arr+newmax;
	while(--enew >= eold) {
	  i_delete(*enew);
	  *enew=(ITEM)NULL;
	}
}

ITEM w_vconv1();

/* w_vconv(terms,hvars,varsonly) - converts old term set
 *	to new term set using hash mapping.
 */

ITEM
w_vconv(terms,hvars,varsonly)
	ITEM terms,hvars;
	PREDICATE varsonly;
	{
	ITEM result,term,*entry;
	LIST *last=L_LAST(result=L_EMPTY);
	LIST_DO(term,terms)
	  if(!varsonly || term->item_type== 'v')
	    last=l_end(w_vconv1(term,hvars),last);
	LIST_END
	return(result);
}

ITEM
w_vconv1(term,hvars)
	ITEM term,hvars;
	{
	ITEM result;
	switch(term->item_type) {
	    case 'f': {
		FUNC f1,f2=(FUNC)I_GET(term);
		ITEM *fptr1,*fptr2;
		result=i_create('f',f1=f_create(F_SIZE(term)));
		FNAME(f1)=i_inc(FNAME(f2));
		ARG_LOOP2(fptr1,fptr2,f1,f2)
		    *fptr1=w_vconv1(*fptr2,hvars);
		}
		break;
	    case 'v': {
		ITEM *entry;
		if(!(*(entry=h_ins(term,hvars))))
		    d_error("w_vconv1 - term not found");
		result=i_create('v',(POINTER)I_GET(*entry));
		}
		break;
	    case 'h': case 'i': case 'r':
		result=i_inc(term);
		break;
	    default:
		d_error("w_vconv1 - bad term type");
	}
	return(result);
}

ITEM ct_sample(),ct_pairs();

/* w_control() - takes a sample of pairs and finds the one which
 *	leads to the construction of a new predicate with the most
 *	compression
 */

PREDICATE
w_control()
	{
	ITEM ex=b_elem(b_first(bfores),spatoms),pair,pred=F_ELEM(0l,ex),
		firstarg=F_ELEM(1l,ex),pairs,goodEs=
		  b_int(b_copy(bfores),F_ELEM(PNO(firstarg->extra),pas)),
		bestatoms=(ITEM)NULL,bestposcov=(ITEM)NULL,atom,sample;
	LONG bestcomp= -9999l;
	PREDICATE increasing=FALSE;
	pairs=ct_pairs(exlim,goodEs,spatoms);
	LIST_DO(pair,pairs)
	  if(w_construct(pair,pred,&bestposcov,&bestcomp,TRUE)) {
	    i_delete(bestatoms);
	    bestatoms=i_inc(pair);
	    increasing=TRUE;
	    break;
	  }
	LIST_END
	if(increasing) {
	  do {
	    i_delete(bestatoms);
	    bestatoms=b_btos(spatoms,bestposcov);
	    increasing=FALSE;
	    b_sub(goodEs,bestposcov);
	    sample=ct_sample(ex,exlim,goodEs);
	    LIST_DO(atom,sample)
	      if(w_construct(l_push(atom,bestatoms),pred,
		  &bestposcov,&bestcomp,TRUE)) {
	        increasing=TRUE;
		break;
	      }
	    LIST_END
	    i_delete(sample);
	  } while(increasing);
	  i_delete(bestatoms);
	  bestcomp=0l;
	  bestatoms=b_btos(spatoms,bestposcov);
	  w_construct(bestatoms,pred,&bestposcov,&bestcomp,FALSE);
	}
	i_deletes(pairs,ex,goodEs,bestatoms,bestposcov,(ITEM)I_TERM);
	return(increasing);
}


/* w_extractas(subs) - returns bitset of covered atoms
 */

ITEM
w_extractas(subs)
	ITEM subs;
	{
	ITEM sub,result=B_EMPTY;
	LIST_DO(sub,subs)
	  b_add(TNO(F_ELEM(0l,sub)->extra),result);
	LIST_END
	return(result);
}
