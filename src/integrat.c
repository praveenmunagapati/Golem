/* ####################################################################### */

/*                      GOLEM Integrate Routines			   */
/*                      ------------------------			   */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/*
 * Golem reads in clauses and integrates them into data structures which
 *	give rapid indexing for particular tasks. The data-structures are
 *	the following hash-tables
 *
 * A path is an integer-array stack of (function-symbol/arg-num) pairs which
 *	specify a particular sub-term of a given term. These are hashed
 *	to give a unique number representing each path. An example of a path might
 *	be [(`f` 2) (`p` 1)], which is the path of term a(b) in p(f(c,a(b),d),e).
 *	The function-symbol and argument number are stored as 2 16bit ints within
 *	a single unsigned long integer for efficiency.
 */

int
cl_readas(fname,batoms)
	STRING fname;
	ITEM *batoms;
	{
	FILEREC *in;
	ITEM i,atom;
	LONG psym,start;
	char mess[MAXMESS];
	if (!(in=frecopen(fname,"r"))) {
		g_message("Cannot find %s",fname);
		return;
	}
	for(;;) {
		i=cl_fread(in,FALSE);
		if(i==(ITEM)I_ERROR) continue;
		else if (i->item_type == 'h' && (LONG)I_GET(i) ==peof)
			break;
		if(!(atom=HOF((LIST)I_GET(i)))) {	/* Headless clause */
			l_pop(i);	/* Remove NULL head */
			start=cputime();
			interp_com(i);
			l_push((ITEM)NULL,i);
			cl_swrite(mess,i);
			g_message("%s - Time taken %ldms",mess,cputime()-start);
		}
		else if(l_length(i)==1) {	/* ATOM */
		  if(atom->item_type== 'f')
			  psym=(LONG)I_GET(F_ELEM(0,atom));
		  else if(atom->item_type== 'h')
			  psym=(LONG)I_GET(atom);
		  else {
			printf("[Syntax error at line %ld in file <%s>]\n",
				in->line_no,in->filename);
			i_delete(i);
			continue;
		  }
		  ct_integrate(atom);
		  b_add(TNO(atom->extra),*batoms);
		}
		else {
		  printf("* Ignoring non-unit clause\n\t");
		  cl_fwrite(ttyout,i); i_fnl(ttyout);
		}
		i_delete(i);
	}
	freclose(in);
	if (*batoms==bfores)
		b_uni(bbacks,bfores);
	i_delete(i);
}

/*
 * ct_integrate - recurse through each term in the given atom,
 *	noting term/path/atom and path/term/atom triples.
 */

int
ct_integrate(atom)
	ITEM atom;
	{
	FUNC f=(FUNC)I_GET(atom);
	LONG n=0l,hp;
	register ITEM *fptr1,*fptr2;
	ITEM path,arg,psym,*mode,*entry;
	LONG anum=b_num(atom,spatoms),pnum;
	*y_ins(anum,asz)=ct_cost(atom);
	atom->extra= PT(NGRND,anum);
	if (atom->item_type == 'h') return; /* 0-arity */
	else if (atom->item_type != 'f') d_error("ct_integrate - bad atom type");
	if (*(mode=h_ins(psym=FNAME(f),modes)))
		fptr2= (((FUNC)I_GET(*mode))->arr)+1;
	else fptr2= (ITEM *)NULL;
	if (!(*(entry=f_ins(pnum=(LONG)I_GET(psym),predatoms))))
		*entry=B_EMPTY;
	b_add(anum,*entry);
	path=Y_EMPTY;
	ARG_LOOP(fptr1,f) {
	    Y_PUSH(hp=PT(pnum,++n),path); hp++;
	    if (fptr2) ct_integrate1(*fptr1,path,hp,anum,*fptr2++);
	    else ct_integrate1(*fptr1,path,hp,anum,(ITEM)NULL);
	    Y_POP(path);
	}
	i_delete(path);
}

/*
 * ct_integrate1 - recurse through term, noting term/path/atom triples.
 */

int
ct_integrate1(term,path,hpath,anum,modev)
	register ITEM path,term,modev;
	LONG anum,hpath;
	{
	register LONG hterm;
	float *real;
	switch(term->item_type) {
	    case 'f':
	      {
		FUNC f=(FUNC)I_GET(term);
		ITEM *fptr,arg;
		LONG n=0l,fsym,sa;
		hterm= (fsym=(LONG)I_GET(FNAME(f)));
		ARG_LOOP(fptr,f) {
		    Y_PUSH(sa=PT(fsym,++n),path);
		    ct_integrate1(*fptr,path,hpath+sa+1l,anum,modev);
		    hterm+=TNO((*fptr)->extra);
		    Y_POP(path);
		}
	      }
	      break;
	    case 'h': case 'i': case 'v':
		hterm=(LONG)I_GET(term);
		break;
	    case 'r':
		real=(float *)I_GET(term);
		hterm= *real;
		break;
	    default:
		d_error("ct_integrate1 - bad term type");
	}
	cl_notepath(term,hterm,path,hpath,anum,modev);
}

/*
 * cl_notepath - path,term and atom are translated into numbers.
 *	Path->term mapping is stored in pts.
 *	Path->atom mapping is stored in pas.
 *	Term->path mapping is stored in tps.
 *	Path/term->atom mapping is stored in ptas.
 */

int
cl_notepath(term,hterm,path,hpath,av,modev)
	ITEM term,path,modev;
	register LONG hterm,hpath,av;
	{
	register LONG pv,tv,pt,*ptp;
	register ITEM *entry,newpath;

	/* Note Path->term */
	if(!(*(entry=f_ins(pv=b_numv(newpath=y_copy(path),hpath,sppaths),pts))))
		*entry=B_EMPTY;
	i_delete(newpath);
	b_add(tv=b_numv(term,hterm,spterms),*entry);

	/* Note Path->atom */
	if(!(*(entry=f_ins(pv,pas))))
		*entry=B_EMPTY;
	b_add(av,*entry);

	/* Note Term->path */
	if(!(*(entry=f_ins(tv,tps))))
		*entry=B_EMPTY;
	b_add(pv,*entry);

	/* Declare mode */
	if (modev && !(*(entry=f_ins(pv,pathio)))) *entry=i_inc(modev);

	/* Note path and term numbers on term */
	term->extra=PT(pv,tv);
	
	/* Find path/term number */
	if(*(ptp=pt_ins(pv,tv))== PTTERM) {
	    *ptp++ =PT(pv,tv);
	    *ptp++ =pt=ptno++;
	    *ptp= PTTERM;
	}
	else pt=GETPT(ptp);

	/* Insert path/term->atom */
	if(!(*(entry=f_ins(pt,ptas))))
		*entry=B_EMPTY;
	b_add(av,*entry);
}

/*
 * cl_integrate/1 - mark each term in clause with path and term numbers.
 */

ITEM
cl_integrate(clause)
	ITEM clause;
	{
	LIST elem;
	FUNC f;
	register ITEM *fptr;
	ITEM atom,path;
	register LONG n,hp,pnum;
	LIST_LOOP(elem,(LIST)I_GET(clause)) {
	  atom=L_GET(elem);
	  if (atom->item_type == 'h') return; /* 0-arity */
	  else if (atom->item_type != 'f') d_error("cl_integrate - bad atom type");
	  f=(FUNC)I_GET(atom);
	  n=0l;
	  path=Y_EMPTY;
	  pnum=(LONG)I_GET(FNAME(f));
	  ARG_LOOP(fptr,f) {
	    Y_PUSH(hp=PT(pnum,++n),path); hp++;
	    cl_integrate1(*fptr,path,hp);
	    Y_POP(path);
	  }
	  i_delete(path);
	}
	return(clause);
}

/* cl_integrate - numbers terms and paths and returns true if
 *	given term is ground. */

PREDICATE
cl_integrate1(term,path,hpath)
	ITEM term,path;
	LONG hpath;
	{
	PREDICATE result=TRUE;
	LONG pv,tv,hterm;
	ITEM newpath;
	float *real;
	switch(term->item_type) {
	    case 'f':
	      {
		FUNC f=(FUNC)I_GET(term);
		ITEM *fptr;
		LONG n=0,sa,fsym;
		hterm= (fsym=(LONG)I_GET(FNAME(f)));
		ARG_LOOP(fptr,f) {
		    Y_PUSH(sa=PT(fsym,++n),path);
		    if(!cl_integrate1(*fptr,path,hpath+sa+1l)) result=FALSE;
		    hterm+=TNO((*fptr)->extra);
		    Y_POP(path);
		}
	      }
	      break;
	    case 'h': case 'i':
		hterm=(LONG)I_GET(term);
		break;
	    case 'r':
		real=(float *)I_GET(term);
		hterm= *real;
		break;
	    case 'v':
		result=FALSE;
		break;
	    default:
		d_error("ct_integrate - bad term type");
	}
	pv=b_numv(newpath=y_copy(path),hpath,sppaths);
	tv=(result?b_numv(term,hterm,spterms):NGRND);
	term->extra=PT(pv,tv);
	i_delete(newpath);
	return(result);
}

/*
 * cl_mdeclare/1 - make mode declaration. Mode should have a form such
 *	as mode(append(+,+,-)), meaning the first 2 args are inputs and
 *	the last is output.
 */

PREDICATE
cl_mdeclare(mode)
	ITEM mode;
	{
	LONG val;
	ITEM *fptr,*entry;
	FUNC f;
	PREDICATE result=TRUE;
	if (mode->item_type != 'f') {
	  printf("[No predicate arguments in mode declaration - ");
	  result=FALSE;
	}
	else {
	  f=(FUNC)I_GET(mode);
	  if (*(entry=h_ins(FNAME(f),modes))) {
	    printf("[Redeclaration of mode ignored - ");
	    result=FALSE;
	  }
	  else {
	    ARG_LOOP(fptr,f) {
	      val=(LONG)I_GET(*fptr);
	      if ((*fptr)->item_type != 'h') {
		result=FALSE;
		break;
	      }
	      else if (val == pplus) {
		(*fptr)->item_type= 'i';
/*
		(LONG)I_GET(*fptr) = IN;
*/
		I_GET(*fptr) = (POINTER)IN;
	      }
	      else if (val == pminus) {
		(*fptr)->item_type= 'i';
/*
		(LONG)I_GET(*fptr) = OUT;
*/
		I_GET(*fptr) = (POINTER)OUT;
	      }
	      else {
	        result=FALSE;
		break;
	      }
	    }
	    if (result) *entry=i_inc(mode);
	  }
	}
	return(result);
}

/*
 * cl_ddeclare/2 - declare determination.
 */

PREDICATE
cl_ddeclare(pred,subpred)
	ITEM pred,subpred;
	{
	LONG val;
	ITEM *fptr,*entry;
	FUNC f;
	PREDICATE result=TRUE;
	if (!(*(entry=h_ins(pred,determs))))
		*entry=L_EMPTY;
	l_push(subpred,*entry);
	return(result);
}

/*
 * cl_ioterms/8 - partitions the terms found in
 *	a clause into input, output and input/output terms
 *		by using mode declarations.
 *	hterms is used to record the mode of terms.
 *	flipio flips input mode to output mode and vv.
 *	usehv indicates whether to use hterms.
 *	varsonly indicates whether terms that are
 *		variables should be taken into account.
 */

int
cl_ioterms(clause,iterms,oterms,hterms,flipio,usehv,varsonly)
	ITEM clause,iterms,oterms,hterms;
	PREDICATE flipio,usehv,varsonly;
	{
	LIST elem;
	FUNC f1,f2;
	ITEM *mode,*fptr1,*fptr2,atom;
	LONG mval;
	LIST_LOOP(elem,(LIST)I_GET(clause)) {
	  if (*(mode=h_ins(FNAME(f1=(FUNC)
		I_GET(atom=L_GET(elem))),modes))) {
	    f2=(FUNC)I_GET(*mode);
	    ARG_LOOP2(fptr1,fptr2,f1,f2) {
	      mval=(flipio?-((LONG)I_GET(*fptr2)):
		(int)I_GET(*fptr2));
	      switch(mval) {
	        case IN:
		  ct_ioterms(*fptr1,iterms,hterms,mval,usehv,varsonly);
		  break;
	        case OUT:
		  ct_ioterms(*fptr1,oterms,hterms,mval,usehv,varsonly);
		  break;
	        default:
		  d_error("ct_ioterms - bad IO mode");
	      }
	    }
	  }
	  else ARG_LOOP(fptr1,f1)
	    ct_ioterms(*fptr1,iterms,hterms,IN,usehv,varsonly);
	}
	set_sub(i_sort(oterms),i_sort(iterms));
}

int
ct_ioterms(term,terms,hterms,mode,usehv,varsonly)
	ITEM term,terms,hterms;
	LONG mode;
	PREDICATE usehv,varsonly;
	{
	LONG modes=mode;
	ITEM *entry,*fptr;
	FUNC f;
	switch(term->item_type) {
	  case 'f':
	    f=(FUNC)I_GET(term);
	    ARG_LOOP(fptr,f) ct_ioterms(*fptr,terms,hterms,mode,usehv,varsonly);
	    break;
	  case 'v':
	    if (varsonly) {
	      if (!usehv) l_push(term,terms);
	      else if (!(*(entry=h_ins(term,hterms)))) {
		*entry=I_INT(modes);
		l_push(term,terms);
	      }
	    }
	    break;
	  case 'i': case 'r': case 'h':
	    break;
	  default:
	    d_error("ct_ioterms - bad term type");
	}
	if (!varsonly) {
	  if (!usehv) l_push(term,terms);
	  else if (!(*(entry=h_ins(term,hterms)))) {
		*entry=I_INT(modes);
		l_push(term,terms);
	  }
	}
}

/*
 * cl_readrls(fname) - read rules from file into rules database.
 */

int
cl_readrls(fname)
	STRING fname;
	{
	FILEREC *in;
	ITEM i;
	if (!(in=frecopen(fname,"r"))) {
		g_message("Cannot find %s",fname);
		return;
	}
	while((i=cl_fread(in,FALSE))==(ITEM)I_ERROR ||
		!(i->item_type== 'h' && (LONG)I_GET(i)==peof)) {
	    if(i==(ITEM)I_ERROR) continue;
	    l_push(i_dec(cl_integrate(i)),rules);
	}
	freclose(in);
	i_sort(rules);
	i_delete(i);
}
