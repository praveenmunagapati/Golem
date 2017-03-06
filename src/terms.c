/* ####################################################################### */

/*                      GOLEM Terms Routines                               */
/*                      --------------------                               */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/*
 * p_vname - creates new variable names from numbers. Conversion is
 *	0,1,..,25,26,27,...   becomes
 *	A,B,.., Z,A0,B0,...
 */

ITEM
p_vname(n)
	LONG n;
	{
	char mess[MAXWORD],c;

	if (0 <= n && n <= 25) sprintf(mess,"%c",c=n + 'A');
	else sprintf(mess,"%c%ld",(n%26)+'A',n/26-1);
	return(i_create('s', (POINTER)strsave(mess)));
}

/*
 * p_write - writes out term in standard Prolog fashion. Used by i_write.
 *	Variables names in order A,B,..,Z,V0,V1,...
 */

#define	GTP(p1,p2,a)	((*a)=='x'?(p1)>(p2):(p1)>=(p2))

p_write(term,put1ch,vtable,vnum,prec,assoc)
	ITEM term;
	LONG (*put1ch) ();
	ITEM vtable;
	LONG *vnum,prec;
	STRING assoc;
	{
	register char mess[MAXWORD];
	FUNC f;
	ITEM *fptr,ffsym;
	STRING name,assoc1;
	PREDICATE alphaname,brackets;
	LONG nargs,pnum,prec1;
	switch(term->item_type) {
	  case 'f':
		f=(FUNC)I_GET(term);
		nargs=F_SIZE(term)-1;
		pnum=(LONG)I_GET(F_ELEM(0l,term));
		name=QP_ntos(pnum);
		ffsym=i_create('h',QP_ston(name,0l));
		if(exp_ap(ffsym,&assoc1,&prec1)) { /* Operator */
			if(brackets= !GTP(prec,prec1,assoc)) {
			    (*put1ch) ('(');
			    charlast=SEP;
			}
			switch(strlen(assoc1)-1) {	/* Arity */
			  case 1:
				if(*assoc1=='f') { /* Prefix */
				    p_swrite(name,pnum,put1ch);
				    p_write(F_ELEM(1l,term),put1ch,vtable,vnum,prec1,assoc1+1);
				}
				else { /* Postfix */
				    p_write(F_ELEM(1l,term),put1ch,vtable,vnum,prec1,assoc1+1);
				    p_swrite(name,pnum,put1ch);
				}
				break;
			  case 2:
			        p_write(F_ELEM(1l,term),put1ch,vtable,vnum,prec1,assoc1);
			        p_swrite(name,pnum,put1ch);
			        p_write(F_ELEM(2l,term),put1ch,vtable,vnum,prec1,assoc1+2);
				break;
			  default:
				d_error("p_write - bad associativity");
			}
			if(brackets= !GTP(prec,prec1,assoc)) {
			    (*put1ch) (')');
			    charlast=SEP;
			}
		}
		else if (pnum==pdot) {	/* List */
			(*put1ch) ('['); charlast=SEP;
			p_lwrite(term,put1ch,vtable,vnum);
			(*put1ch) (']'); charlast=SEP;
		}
		else {
			p_swrite(name,pnum,put1ch);
			(*put1ch) ('('); charlast=SEP;
			ARG_LOOP(fptr,f) {
				p_write(*fptr,put1ch,vtable,vnum,250l,"fx");
				if(--nargs) {
				    (*put1ch) (',');
				    charlast=SEP;
				}
			}
			(*put1ch) (')'); charlast=SEP;
		}
		i_delete(ffsym);
		break;
	  case 'h':
		name=QP_ntos(pnum=(LONG)I_GET(term));
		p_swrite(name,pnum,put1ch);
		break;
	  case 'v':
		if (vtable) {
		    ITEM num=i_create('i',(POINTER)I_GET(term)),*entry;
		    if(!(*(entry=h_ins(num,vtable)))) /* Already seen this variable */
		        *entry= p_vname((*vnum)++);
		    p_swrite((STRING)I_GET(*entry),INF,put1ch);
		    i_delete(num);
		}
		else {
		    sprintf(mess,"_%ld",(POINTER)I_GET(term));
		    p_swrite(mess,INF,put1ch);
		}
		break;
	  case 'i':
		sprintf(mess,"%ld",(LONG)I_GET(term));
		p_swrite(mess,INF,put1ch);
		break;
	  case 'r':
		sprintf(mess,"%.2f",*((float *)I_GET(term)));
		p_swrite(mess,INF,put1ch);
		break;
	  default:
		d_error("p_write - illegal term type");
	}
}

p_swrite(name,pnum,put1ch)
	STRING name;
	LONG pnum;
	LONG (*put1ch) ();
	{
	PREDICATE unquoted,symbolic=lsymbol(name),num=number(name);
	register char *sp;
	unquoted=(symbolic||num||ualphanum(name)||lalphanum(name)||pnum==pempty);
	if(unquoted && charlast!=SEP && ((symbolic && charlast==SYM) ||
		(!symbolic && charlast==ALPHN) ||
		(num && charlast==ALPHN))) (*put1ch) (' ');
	if (!unquoted) (*put1ch) ('\'');
	STR_LOOP(sp,name) (*put1ch) (*sp);
	if (!unquoted) {(*put1ch) ('\''); charlast=SEP;}
	else charlast= (symbolic?SYM:ALPHN);
}

/*
 * p_lwrite - write out the internals of a Prolog list (without brackets)
 */

p_lwrite(term,put1ch,vtable,vnum)
	ITEM term;
	LONG (*put1ch) ();
	ITEM vtable;
	LONG *vnum;
	{
	for(;;) {	/* Loop through a Prolog list */
		p_write(F_ELEM(1l,term),put1ch,vtable,vnum,250l,"fx");
		term=F_ELEM(2l,term);
		if(term->item_type == 'f' && (LONG)I_GET(F_ELEM(0l,term))==pdot)
			{(*put1ch) (','); charlast=SEP;}
		else break;
	}
	if (!(term->item_type == 'h' && (LONG)I_GET(term)==pempty)) {
		(*put1ch) ('|'); charlast=SEP;
		p_write(term,put1ch,vtable,vnum,250l,"fx");
	}
}

extern FILEREC *glob_file;
extern LONG line_cnt;
extern put1tfile();
extern PREDICATE instring;

/*
 * p_fwrite - writes clause to given file in Prolog format.
 */

int
p_fwrite(out,i)
	FILEREC *out;
	ITEM i;
	{
	ITEM vtable=h_create(3l);
	LONG vnum=0l;
	line_cnt=0l;
	instring=FALSE;
	glob_file=out;
	charlast=SEP;
	p_write(i,put1tfile,vtable,&vnum,250l,"fx");
	frecflush(glob_file);
	i_delete(vtable);
}

/* ####################################################################### 
 *
 * p_read/5 - reads any Prolog term
 */


#define		START		0
#define		STR		1
#define		INTGR		2
#define		REAL		3
#define		ARGS_START	4
#define		ARG_SEP		5
#define		ARG		6
#define		VRBL		7
#define		ATM		8
#define		LIST_ELEM	9
#define		LIST_SEP	10
#define		LIST_FIN	11
#define		DCARE		12

PREDICATE exp_operator();
PREDICATE exp_ap();

ITEM
p_read(get1ch,unget1ch,vtable,toplevel,terminator,expect)
	char (*get1ch) ();
	LONG (*unget1ch) ();
	ITEM vtable;
	PREDICATE toplevel;
	LONG *terminator,expect;
	{
	register char c;
	int state=START;
	char str[MAXWORD];
	register STRING strp;
	LONG nargs,subtermin;
	PREDICATE term_started=FALSE,symbol_atom=FALSE;
	ITEM subterm,term=(ITEM)NULL,termlist=(ITEM)NULL,
		*fptr,*lelem,*lrest;
	FUNC f;
	LIST *last;
	while (c = (*get1ch) ()) {
		switch (state) {
		    case START:
			switch (c) {
			    case ' ': case '\t': case '\n': /* White space */
				break;
			    case '%':	/* Comment till end of line */
				while (((*get1ch) ()) != '\n');
				break;
			    case '_':			/* Variable */
				term_started=TRUE;
				strp=str;
				*strp++ = c;
				state=VRBL;
				break;
			    case '0': case '1': case '2': case '3': case '4':
			    case '5': case '6': case '7': case '8': case '9':
				term_started=TRUE;	/* Integer */
				strp=str;
				*strp++ = c;
				state=INTGR;
				break;
			    case '\'':	/* Atom or compound */
				term_started=TRUE;
				strp=str;
				state=STR;
				break;
			    case '[':	/* List */
				term_started=TRUE;
				if ((c=(*get1ch) ())== ']') {
					term = i_create('h',(POINTER)pempty);
					return(term);
				}
				else (*unget1ch) (c);
				term=i_create('f',(POINTER)(f=f_create(3l)));
				fptr=f->arr;
				*fptr++ = i_create('h',(POINTER)pdot);
				*(lelem=fptr++) = (ITEM)NULL;
				*(lrest=fptr) = (ITEM)NULL;
				state=LIST_ELEM;
				break;
			    case ',':
				if(!toplevel) {*terminator=pcomma; return((ITEM)I_ERROR);}
			    case '+': case '-': case '*': case '/': case '\\': case '^':
			    case '<': case '>': case '=': case '`': case '~': case ':':
			    case '.': case '?': case '@': case '#': case '$': case '&': 
			    case '!':
				symbol_atom=TRUE;
			    case 'a': case 'b': case 'c': case 'd': case 'e': case 'f':
			    case 'g': case 'h': case 'i': case 'j': case 'k': case 'l':
			    case 'm': case 'n': case 'o': case 'p': case 'q': case 'r':
			    case 's': case 't': case 'u': case 'v': case 'w': case 'x':
			    case 'y': case 'z':
				term_started=TRUE;
				strp=str;
				*strp++ = c;
				if ((c== '-' || c== '+') && expect==OPND) {
					c=(*get1ch) ();
					if(DIGIT(c)) state=INTGR;
					else state=ATM;
					(*unget1ch) (c);
				}
				else state=ATM;
				break;
			    default:
				if (UPCASE(c)) {		/* Variable */
					term_started=TRUE;
					strp=str;
					*strp++ = c;
					state=VRBL;
				}
				else return((ITEM)I_ERROR);
				break;
			}
			break;
		    case ATM:
			switch(c) {
			    case '+': case '-': case '*': case '/': case '\\': case '^':
			    case '<': case '>': case '=': case '`': case '~': case ':':
			    case '.': case '?': case '@': case '#': case '$': case '&': 
			    case '!':
				if (symbol_atom) *strp++ = c;
				else {
					(*unget1ch) (c);
					*strp = '\0';
					term = i_create('h',(POINTER)QP_ston(str,0l));
					if(exp_operator(term)) return(term);
					state= ARGS_START;
				}
				break;
			    default:
				if(ALPHANUM(c) && !symbol_atom) *strp++ = c;
				else {
				  (*unget1ch) (c);
				  *strp = '\0';
				  if(!toplevel) {
				    if(STREQ(str,":-"))
					{*terminator=pif; return((ITEM)I_ERROR);}
				    else if(STREQ(str,"."))
					{*terminator=pdot0; return((ITEM)I_ERROR);}
				    else if(STREQ(str,","))
				    	{*terminator=pcomma; return((ITEM)I_ERROR);}
				  }
				  term = i_create('h',(POINTER)QP_ston(str,0l));
				  if(exp_operator(term)) return(term);
				  state= ARGS_START;
				}
			}
			break;
		    case STR:
			if (c == '\\') *strp++ = (*get1ch) ();
			else if (c == '\'') {
				*strp = '\0';
				term = i_create('h',(POINTER)QP_ston(str,0l));
				if(exp_operator(term)) return(term);
				state= ARGS_START;
			}
			else	*strp++ = c;
			break;
		    case INTGR:
			switch(c) {
			    case '0': case '1': case '2': case '3': case '4':
			    case '5': case '6': case '7': case '8': case '9':
				*strp++ = c;
				break;
			    case '.':
				c=(*get1ch) ();
				if(!DIGIT(c)) {
				    LONG v;
				    (*unget1ch) (c); (*unget1ch) ('.');
				    *strp = '\0';
				    sscanf(str,"%ld",&v);
				    term = i_create('i',(POINTER)v);
				    return(term);
				}
				*strp++ = '.';
			    case 'e': case 'E':
				*strp++ = c;
				state = REAL;
				break;
			    default:
				{LONG v;
				  (*unget1ch) (c);
				  *strp = '\0';
				  sscanf(str,"%ld",&v);
				  term = i_create('i',(POINTER)v);
				  return(term);
				}
			}
			break;
		    case REAL:
			switch(c) {
			    case '0': case '1': case '2': case '3': case '4':
			    case '5': case '6': case '7': case '8': case '9':
			    case 'e': case 'E': case '-':
				*strp++ = c;
				break;
			    default:
				{float v, *vp;
				  (*unget1ch) (c);
				  *strp = '\0';
				  sscanf(str,"%f",&v);
				  vp = r_create(v);
				  term = i_create('r',(POINTER)vp);
				  return(term);
				}
			}
			break;
		    case ARGS_START:
			if (c == '(') {
				i_delete(term);
				nargs=0l;
				last = L_LAST(termlist=L_EMPTY);
				state = ARG;
			}
			else {
				(*unget1ch) (c);
				return(term);
			}
			break;
		    case ARG:
			(*unget1ch) (c);
			subtermin=(LONG)I_ERROR;
			if ((subterm=exp_read(get1ch,unget1ch,vtable,
				FALSE,&subtermin))==(ITEM)I_ERROR) {
			    i_delete(termlist);
			    return((ITEM)I_ERROR);
			}
			last=l_end(subterm,last);
			nargs++;
			if(subtermin!=pcomma) state=ARG_SEP;
			break;
		    case ARG_SEP:
			switch(c) {
			    case ' ': case '\t': case '\n': /* White space */
				break;
			    case '%':	/* Comment till end of line */
				while (((*get1ch) ()) != '\n');
				break;
			    case ')':
				l_push(i_dec(i_create('h',(POINTER)QP_ston(str,nargs))),
					termlist);
				term = f_ltof(termlist);
				i_delete(termlist);
				return(term);
				break;
			    default:
				i_delete(termlist);
				return((ITEM)I_ERROR);
			}
			break;
		    case LIST_ELEM:
			(*unget1ch) (c);
			subtermin=(LONG)I_ERROR;
			if ((*lelem=exp_read(get1ch,unget1ch,vtable,
				FALSE,&subtermin))==(ITEM)I_ERROR) {
			    i_delete(term);
			    return((ITEM)I_ERROR);
			}
			if(subtermin==pcomma) {
			    *lrest=i_create('f',(POINTER)(f=f_create(3l)));
			    fptr=f->arr;
			    *fptr++ = i_create('h',(POINTER)pdot);
			    *(lelem=fptr++) = (ITEM)NULL;
			    *(lrest=fptr) = (ITEM)NULL;
			}
			else state=LIST_SEP;
			break;
		    case LIST_SEP:
			switch(c) {
			    case ' ': case '\t': case '\n': /* White space */
				break;
			    case '%':	/* Comment till end of line */
				while (((*get1ch) ()) != '\n');
				break;
			    case '|':
				if ((*lrest=exp_read(get1ch,unget1ch,vtable,
					TRUE,&subtermin))==(ITEM)I_ERROR) {
				    i_delete(term);
				    return((ITEM)I_ERROR);
				}
				state=LIST_FIN;
				break;
			    case ']':
				*lrest = i_create('h',(POINTER)pempty);
				return(term);
				break;
			    default:
				i_delete(term);
				return((ITEM)I_ERROR);
			}
			break;
		    case LIST_FIN:
			switch(c) {
			    case ' ': case '\t': case '\n': /* White space */
				break;
			    case '%':	/* Comment till end of line */
				while (((*get1ch) ()) != '\n');
				break;
			    case ']':
				return(term);
				break;
			    default:
				i_delete(term);
				return((ITEM)I_ERROR);
			}
			break;
		    case VRBL:	/* Variable names are mapped to unique no. using hash table */
			if (ALPHANUM(c)) *strp++ = c;
			else {
			    LONG *vp= (LONG *)&(I_GET(varno));
			    (*unget1ch) (c);
			    *strp = '\0';
			    if (STREQ(str,"_")) {
				term = i_create('v',(POINTER)*vp);
				(*vp)++;
			    }
			    else {
				ITEM name=i_create('s',(POINTER)strsave(str)),
					*entry;
				if (!(*(entry=h_ins(name,vtable)))) /* New var */
				    *entry= I_INT((*vp)++);
				term = i_create('v',(POINTER)I_GET(*entry));
				i_delete(name);
			    }
			    return(term);
			}
			break;
		    default:
			d_error("p_read - bad state number");
		}
	}
	if (term_started)
		d_error("p_read - unexpected end of input");
	i_deletes(term,termlist,(ITEM)I_TERM);
	return((ITEM)I_ERROR);
}

extern char get1ftty();
extern int unget1ftty();

ITEM
p_ttyread()
	{
	ITEM result,vtable=h_create(3l);
	LONG terminator;
	if ((result=p_read(get1ftty,unget1ftty,vtable,TRUE,&terminator,OPND))==(ITEM)I_ERROR)
		while(get1ftty() != '\n');	/* Ignore line */
	i_delete(vtable);
	return(result);
}

/* ####################################################################### 
 *
 * exp_read/2 - reads any Prolog expression
 */


#define		CLOSEB		1l

LONG exp_update();
PREDICATE exp_collapse();

ITEM
exp_read(get1ch,unget1ch,vtable,toplevel,terminator)
	char (*get1ch) ();
	LONG (*unget1ch) ();
	ITEM vtable;
	PREDICATE toplevel;
	LONG *terminator;
	{
	register char c;
	LONG state=START,expect=OPND,subtermin;
	ITEM result=(ITEM)NULL,term=(ITEM)NULL,optrs=L_EMPTY,opnds=L_EMPTY;
	while (c = (*get1ch) ()) {
		switch (state) {
		    case START:
			switch(c) {
			    case ' ': case '\t': case '\n': /* White space */
				break;
			    case '%':	/* Comment till end of line */
				while (((*get1ch) ()) != '\n');
				break;
			    case '(': /* Open subexpression */
				if((term=exp_read(get1ch,unget1ch,vtable,
					TRUE,&subtermin))==(ITEM)I_ERROR) {
				    i_deletes(optrs,opnds,(ITEM)I_TERM);
				    return((ITEM)I_ERROR);
				}
				state=CLOSEB;
				break;
			    default:
			        (*unget1ch) (c);
				*terminator=(LONG)I_ERROR;
				if((term=p_read(get1ch,unget1ch,vtable,
					toplevel,terminator,expect))==(ITEM)I_ERROR) {
				    if(*terminator==(LONG)I_ERROR) (*unget1ch) (c);
				    if(exp_collapse(optrs,opnds,INF,"xfx")&&(l_length(opnds)==1l))
					    result=l_pop(opnds);
				    else result=(ITEM)I_ERROR;
				    i_deletes(optrs,opnds,(ITEM)I_TERM);
				    return(result);
				}
				if((expect=exp_update(term,expect,optrs,opnds))==(LONG)I_ERROR) {
				    i_deletes(term,optrs,opnds,(ITEM)I_TERM);
				    return((ITEM)I_ERROR);
				}
				i_delete(term);
				break;
			}
			break;
		    case CLOSEB:
			if(c!=')' || (expect=exp_update(term,expect,optrs,opnds))==(LONG)I_ERROR) {
			    i_deletes(term,optrs,opnds,(ITEM)I_TERM);
			    return((ITEM)I_ERROR);
			}
			i_delete(term);
			state=START;
			break;
		    default:
			d_error("exp_read - bad state number");
		}
	}
	i_deletes(result,term,optrs,opnds,(ITEM)I_TERM);
	return((ITEM)I_ERROR);
}

/* exp_update/4 - updates the operator and operand stacks */

PREDICATE exp_prefix();
LONG exp_prec();

LONG
exp_update(term,expect,optrs,opnds)
	ITEM term,optrs,opnds;
	LONG expect;
	{
	STRING assoc;
	LONG prec;
	switch(expect) {
	  case OPND:
	    if(exp_prefix(term)) l_push(term,optrs);
	    else {
	      l_push(term,opnds);
	      expect=OPTR;
	    }
	    break;
	  case OPTR:
	    if(!exp_ap(term,&assoc,&prec)|| *assoc=='f') return((LONG)I_ERROR);
	    if(!L_EMPTYQ(optrs)&&GTP(prec,exp_prec(HOF((LIST)I_GET(optrs))),assoc))
		if(!exp_collapse(optrs,opnds,prec,assoc)) return((LONG)I_ERROR);
	    l_push(term,optrs);
	    expect=(strlen(assoc)==3?OPND:OPTR);
	    break;
	  default:
	    d_error("exp_update - bad expectation value");
	}
	return(expect);
}

/* exp_operator/1 - decides whether term is an operator */

PREDICATE
exp_operator(term)
	ITEM term;
	{
	ITEM *entry;
	if(term->item_type!='h') return(FALSE);
	else if (!(*(entry=f_ins((ITEM)I_GET(term),ops)))) return(FALSE);
	return(TRUE);
}

PREDICATE
exp_ap(term,assoc,prec)
	ITEM term;
	STRING *assoc;
	LONG *prec;
	{
	ITEM *entry;
	if(term->item_type!='h') return(FALSE);
	else if (!(*(entry=f_ins((ITEM)I_GET(term),ops)))) return(FALSE);
	*assoc=(STRING)I_GET(F_ELEM(0l,*entry));
	*prec=(LONG)I_GET(F_ELEM(1l,*entry));
	return(TRUE);
}

/* exp_prefix/1 - decides whether an operator is prefix */

PREDICATE
exp_prefix(term)
	ITEM term;
	{
	ITEM *entry;
	if(term->item_type!='h') return(FALSE);
	else if (!(*(entry=f_ins((ITEM)I_GET(term),ops)))) return(FALSE);
	else if (*((STRING)I_GET(F_ELEM(0l,*entry)))!='f') return(FALSE);
	return(TRUE);
}

LONG
exp_prec(term)
	ITEM term;
	{
	STRING assoc;
	LONG prec;
	exp_ap(term,&assoc,&prec);
	return(prec);
}

LONG
exp_arity(term)
	ITEM term;
	{
	STRING assoc;
	LONG prec;
	exp_ap(term,&assoc,&prec);
	return(strlen(assoc)-1);
}

/* exp_collapse/3 - collapses operator and operand stacks until either
 *	one of them is empty or the term's precedence is less than that
 *	at the top of the operator stack.
 */

PREDICATE
exp_collapse(optrs,opnds,prec,assoc)
	ITEM optrs,opnds;
	LONG prec;
	STRING assoc;
	{
	LONG arity,cnt;
	ITEM op,terml,term,function;
	while(!L_EMPTYQ(optrs)&&!L_EMPTYQ(opnds)&&
		GTP(prec,exp_prec(HOF((LIST)I_GET(optrs))),assoc)) {
	    op=l_pop(optrs); arity=exp_arity(op);
	    terml=L_EMPTY;
	    for(cnt=1l;cnt<=arity;cnt++)
		if(L_EMPTYQ(opnds)) {
		    i_deletes(op,terml,(ITEM)I_TERM);
		    return(FALSE);
		}
		else l_push(i_dec(l_pop(opnds)),terml);
	    function=i_create('h',QP_ston(QP_ntos((LONG)I_GET(op)),arity));
	    l_push(term=f_ltof(l_push(function,terml)),opnds);
	    i_deletes(op,terml,function,term,(ITEM)I_TERM);
	}
	return(TRUE);
}
