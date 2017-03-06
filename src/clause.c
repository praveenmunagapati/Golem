/* ####################################################################### */

/*                      GOLEM Clause Routines                              */
/*                      ---------------------                              */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/*
 * cl_read - reads in a clause from a file. If file ended then
 *	returns item end_of_file.
 */

#define START	0
#define MINUS	2
#define BELEM	4

ITEM
cl_read(get1ch,unget1ch,bodyonly)
	char (*get1ch) ();
	LONG (*unget1ch) ();
	PREDICATE bodyonly;
	{
	register char c,state;
	ITEM result=i_create('l',(POINTER)NULL),term=(ITEM)NULL,vtable=h_create(3l);
	register LIST *last= ((LIST *)&I_GET(result));
	PREDICATE cl_started=FALSE;
	LONG terminator;
	/*
	(LONG)I_GET(varno)=0l;
	I_GET(varno)=(LONG)0;
	*/
	I_ASSIGN(varno,0);
	if(bodyonly) {
		state=BELEM;
		last=l_end((ITEM)NULL,last);
		while((c=(*get1ch)()) == '\n'); /* Clear newlines */
		(*unget1ch)(c);
	}
	else state=START;
	while (c = (*get1ch) ()) {
		switch (state) {
		    case START:
			switch (c) {
			    case ' ': case '\t': case '\n': /* White space */
				break;
			    case '%':	/* Comment till end of line */
				while (((*get1ch) ()) != '\n');
				break;
			    case '!': case ':':	/* headless body */
				last=l_end((ITEM)NULL,last);
				cl_started=TRUE;
				state=MINUS;
				break;
			    default:
				(*unget1ch) (c);
				cl_started=TRUE;
				if ((term=exp_read(get1ch,unget1ch,vtable,FALSE,
					&terminator))==(ITEM)I_ERROR) {
				    i_deletes(result,vtable,(ITEM)I_TERM);
				    return((ITEM)I_ERROR);
				}
				else last=l_end(term,last);
				if(terminator==pif) state=BELEM;
				else if(terminator==pdot0) {
				    i_delete(vtable);
				    return(result);
				}
				else {
				    i_deletes(result,vtable,(ITEM)I_TERM);
				    return((ITEM)I_ERROR);
				}
			}
			break;
		    case MINUS:
			if (c == '-') {
			    state=BELEM;
			}
			else {
			    (*unget1ch) (c);
			    i_deletes(result,vtable,(ITEM)I_TERM);
			    return((ITEM)I_ERROR);
			}
			break;
		    case BELEM:
			cl_started=TRUE;
		        (*unget1ch) (c);
			if ((term=exp_read(get1ch,unget1ch,vtable,FALSE,
				&terminator))==(ITEM)I_ERROR) {
			    i_deletes(result,vtable,(ITEM)I_TERM);
			    return((ITEM)I_ERROR);
			}
			else last=l_end(term,last);
			if(terminator==pcomma) state=BELEM;
			else if (terminator==pdot0) {
			    i_delete(vtable);
			    return(result);
			}
			else {
			    i_deletes(result,vtable,(ITEM)I_TERM);
			    return((ITEM)I_ERROR);
			}
			break;
		    default:
			d_error("cl_read - bad state number");
		}
	}
	if (cl_started)
		d_error("cl_read - unexpected end of input");
	i_deletes(result,vtable,(ITEM)I_TERM);
	return(i_create('h',(POINTER)peof));
}

/*
 * cl_fread - reads a Prolog clause from the given file.
 */

extern FILEREC *glob_file;
extern char get1ffile();
extern unget1ffile();

ITEM
cl_fread(in,bodyonly)
	FILEREC *in;
	PREDICATE bodyonly;
	{
	register ITEM result;
	char c;
	glob_file = in;
	result = cl_read(get1ffile,unget1ffile,bodyonly);
	if (result == (ITEM)I_ERROR || result == (ITEM)I_TERM) {
		printf("[Syntax error at line %ld in file <%s>]\n",
			glob_file->line_no,glob_file->filename);
		while((c=get1ffile()) != '\n' && c!=EOF); /* Ignore line */
		unget1ffile();
	}
	return(result);
}

extern char get1ftty();
extern unget1ftty();

ITEM
cl_ttyread(bodyonly)
	PREDICATE bodyonly;
	{
	ITEM result;
	register char c;
	result = cl_read(get1ftty,unget1ftty,bodyonly);
	if (result == (ITEM)I_ERROR) {
		printf("[Syntax error]\n");
		while((c=get1ftty()) != '\n' && c!=EOF);	/* Ignore line */
		unget1ftty(c);
	}
	return(result);
}

/*
 * cl_write - write out a clause in standard Prolog form.
 */

int
cl_write(i,put1ch)
	ITEM i;
	LONG (*put1ch) ();
	{
	LIST lits=(LIST)I_GET(i),body=TOF(lits),elem;
	ITEM head=(ITEM)HOF(lits),lit;
	ITEM vtable=h_create(3l);
	LONG vnum=0l;

	if (i->item_type != 'l')
		d_error("cl_write - not passed a list");
	charlast=SEP;
	if (head) p_write(head,put1ch,vtable,&vnum,INF,"fx");
	if (head && body) (*put1ch) (' ');
	if (body) {
		(*put1ch) (':'); (*put1ch) ('-'); (*put1ch) (' ');
		PENL_LOOP(elem,body) {
		    lit= L_GET(elem);
		    charlast=SEP;
		    p_write(lit,put1ch,vtable,&vnum,INF,"fx");
		    (*put1ch) (','); (*put1ch) (' ');
		}
		lit= L_GET(elem);
		charlast=SEP;
		p_write(lit,put1ch,vtable,&vnum,INF,"fx");
	}
	(*put1ch) ('.');
	i_delete(vtable);
}

extern LONG line_cnt;
extern put1tfile();
extern PREDICATE instring;

/*
 * cl_fwrite - writes clause to given file in Prolog format.
 */

int
cl_fwrite(out,i)
	FILEREC *out;
	ITEM i;
	{
	line_cnt=0l;
	instring=FALSE;
	glob_file=out;
	charlast=SEP;
	cl_write(i,put1tfile);
	frecflush(glob_file);
}

cl_print(clause)
	ITEM clause;
	{
	cl_fwrite(ttyout,clause);
	printf("\n");
}

extern STRING glob_str;
extern int put1tstring();

int
cl_swrite(s,i)
	STRING s;
	ITEM i;
	{
	glob_str = s;
	cl_write(i,put1tstring);
	put1tstring('\0');
}

int
at_fwrite(out,atom)
	FILEREC *out;
	ITEM atom;
	{
	ITEM clause;
	cl_fwrite(out,clause=l_push(atom,L_EMPTY));
	i_delete(clause);
}

int
cl_showas(out,atoms)
	ITEM atoms;
	FILEREC *out;
	{
	register LIST elem;
	LIST_LOOP(elem,(LIST)I_GET(atoms)) {
		at_fwrite(out,L_GET(elem)); i_fnl(out);
	}
}

int
cl_showrls(out,rls)
	ITEM rls;
	FILEREC *out;
	{
	register LIST elem;
	LIST_LOOP(elem,(LIST)I_GET(rls)) {
		cl_fwrite(out,L_GET(elem));
		i_fnl(out);
	}
}

/*
 * cl_extractas(subs) - extracts a sorted list of atoms from the given
 *	list of substitutions (proofs).
 */

ITEM
cl_extractas(subs)
	ITEM subs;
	{
	ITEM result;
	register LIST elem,*last=L_LAST(result=L_EMPTY);
	LIST_LOOP(elem,(LIST)I_GET(subs))
	    last=l_end(i_inc(F_ELEM(0l,L_GET(elem))),last);
	return(i_sort(result));
}
