#include <stdio.h>
#include "golem.h"

/*
 * #######################################################################
 *
 *                      Item Processing Routines
 *                      ------------------------
 *
 * #######################################################################
 */

#ifdef MEMCHECK
ITEM all_items;
#endif

/* ####################################################################### 
 *
 * i_copy/1 - recursively produces a copy of an item.
 */

ITEM
i_copy(i)
	ITEM i;
	{
	ITEM result;
	register ITEM *felem1,*felem2;
	register LIST elem,*last;
	FUNC f1,f2;
	if (!i) return((ITEM)NULL);
	else {
		switch (i->item_type) {
		    case 'i': case 'r': case 'a': case 's':
		    case 'h': case 'v':
			result=i_create(i->item_type,(POINTER)I_GET(i));
			break;
		    case 'b': case 'y':
			result=b_copy(i);
			break;
		    case 'l':
			last=L_LAST(result=L_EMPTY);
			LIST_LOOP(elem,(LIST)I_GET(i))
				last=l_end(i_copy(L_GET(elem)),last);
			break;
		    case 'f':
			result=i_create('f',
			    (POINTER)f_create(((FUNC)I_GET(i))->arr_size));
			f1=(FUNC)I_GET(result); f2=(FUNC)I_GET(i);
			FUNC_LOOP2(felem1,felem2,f1,f2)
				*felem1= i_copy(*felem2);
			break;
		    default:
			d_error("i_copy - bad item type");
		}
	}
	return(result);
}

/* ####################################################################### 
 *
 * i_cmp/2 - recursively compares two items and says whether the first
 *	is greater than (GT) equal to (EQ) or less than (LT) the second
 */

LONG
i_cmp(i1,i2)
	register ITEM i1,i2;
	{
	LONG result;
	LONG int_cnt,sz1,sz2;
	float *r1,*r2;
	FUNC f1,f2;
	register LIST e1,e2;
	register ITEM *fe1,*fe2;
	register BLOCK bp1,bp2,be1,be2,b1,b2;

	if (i1 == i2) return(EQ);
	else if (!i1) return(LT);
	else if (!i2) return(GT);
	else if (i1->item_type != i2->item_type)
		return((i1->item_type > i2->item_type) ? GT : LT);
	else {
	    switch(i1->item_type) {
		case 'h':	/* Prolog name */
		case 'i':	/* Integer */
		case 'v':	/* Prolog variable */
		    if ((LONG)I_GET(i1) == (LONG)I_GET(i2)) result=EQ;
		    else
			result=(((LONG)I_GET(i1)>(LONG)I_GET(i2))?GT:LT);
		    break;
		case 'r':	/* Float */
		    r1 = (float *)(I_GET(i1)); r2 = (float *)(I_GET(i2));
		    if (*r1 == *r2) result=EQ;
		    else
			result=((*r1 > *r2)?GT:LT);
		    break;
		case 'a':	/* Atom */
		case 's':	/* String */
		    result=strcmp((STRING)I_GET(i1),(STRING)I_GET(i2));
		    if (result) result=(result>0 ? GT : LT);
		    break;
		case 'f':	/* Functor */
		    f1=(FUNC)I_GET(i1); f2=(FUNC)I_GET(i2);
		    FUNC_LOOP2(fe1,fe2,f1,f2) {
			switch(result=i_cmp(*fe1,*fe2)) {
			    case EQ:
				break;
			    case LT:
			    case GT:
				return(result);
			    default:
				d_error("i_cmp - invaid inequality value");
			}
		    }
		    if (fe1 >= (f1->arr + f1->arr_size)) {
			if (fe2 >= (f2->arr + f2->arr_size)) result=EQ;
			else result=LT;
		    }
		    else result=GT;
		    break;
		case 'b':	/* Block */
		case 'y':	/* Integer array */
		    b1=(BLOCK)I_GET(i1); b2=(BLOCK)I_GET(i2);
		    BLOCK_LOOP2(bp1,bp2,be1,be2,b1,b2) {
			if (*bp1 > *bp2) return(GT);
			else if (*bp1 < *bp2) return(LT);
		    }
		    if ((sz1=b_size(i1))==(sz2=b_size(i2))) result=EQ;
		    else result=((sz1>sz2)?GT:LT);
		    break;
		case 'l':	/* List */
		   { ITEM h1,h2,f1,f2; LONG l1,l2;
		    /* Test for correct clause ordering */
		    if(!L_EMPTYQ(i1)&& !L_EMPTYQ(i2)&&
			(h1=HOF((LIST)I_GET(i1)))->item_type== 'f' &&
			(h2=HOF((LIST)I_GET(i2)))->item_type== 'f' &&
			(f1=F_ELEM(0l,h1))->item_type== 'h' &&
			(f2=F_ELEM(0l,h2))->item_type== 'h' &&
			(LONG)I_GET(f1)==(LONG)I_GET(f2) &&
			(l1=l_length(i1))!=(l2=l_length(i2)))
				result=(l1>l2?GT:LT);
		    else {
		      LIST_LOOP2(e1,e2,(LIST)I_GET(i1),(LIST)I_GET(i2)) {
			switch (result=i_cmp((ITEM)L_GET(e1),(ITEM)L_GET(e2))) {
			    case EQ:
				break;
			    case LT:
			    case GT:
				return(result);
			    default:
				d_error("i_cmp - invalid inequality value");
			}
		      }
		      if (!e1) {
			if (!e2) result=EQ;
			else result=LT;
		      }
		      else result=GT;
		    }
		    break;
		   }
		/*
		case 'h':	Prolog name
		    if ((LONG)I_GET(i1) == (LONG)I_GET(i2))
			result= EQ;
		    else {
			result=strcmp(QP_ntos((LONG)I_GET(i1)),
			    QP_ntos((LONG)I_GET(i2)));
			result=(result>0 ? GT : LT);
		    }
		    break;
		*/
		default:
		    d_error("i_cmp - invalid item type");
	    }
	}
	return(result);
}

/* ####################################################################### 
 *
 * i_inc/1 - increments the usage counter of the item and returns the item
 */

ITEM
i_inc(item)
	register ITEM item;
	{
	if (!item) return((ITEM)NULL);
	else if (item->usage >= 65535)
		d_error("i_inc - usage counter overflow");
	else item->usage++;
	return(item);
}
/* ####################################################################### 
 *
 * i_dec/1 - decrements the usage counter of the item and returns the item
 */

ITEM
i_dec(item)
	register ITEM item;
	{
	if (!item) return((ITEM)NULL);
	else if (item->usage == 0)
		d_error("i_dec - usage counter underflow");
	else item->usage--;
	return(item);
}

#define ADDR	1

ITEM
i_create(itype,val) 
	char itype;
	POINTER val;
	{
	ITEM item;
	LIST *hlast;
	char mess[MAXMESS];
#ifdef MEMCHECK
	ITEM *hplace;
	LIST lptr;

	sprintf(mess,"i_create %c",itype);
#endif
        if (!(item = (ITEM)GOLEM_CALLOC(1l, sizeof(struct item), mess)))
		d_error("i_create - calloc failure");
	else {
		item->item_type=itype;
		item->usage=1;
		item->obj=val;
		item->extra=UNASS;
#ifdef MEMCHECK
		hplace= &(((FUNC)I_GET(all_items))->arr[h_add_hfn(item,all_items)]);
		if (!(*hplace)) {
			if (!(*hplace = (ITEM)GOLEM_CALLOC(1l, sizeof(struct item), "i_create 1")))
				d_error("i_create - calloc failure");
			(*hplace)->item_type= 'l';
			(*hplace)->usage=1;
			(*hplace)->obj=(POINTER)NULL;
			hlast=L_LAST(*hplace);
		}
		else
		    LISTP_LOOP(hlast,*hplace)
			if (item == L_GET(*hlast)) break;
		if (!(lptr = (LIST)GOLEM_CALLOC(1l, sizeof(struct lmem), "i_create 2")))
			d_error("i_create - calloc failure 2");
		lptr->pres= item;
		lptr->next= *hlast;
		*hlast= lptr;
#endif
	}
	return(item);
}

#ifdef MEMCHECK
int
i_print_all()
	{
	register ITEM *felem;
	FUNC f= (FUNC)I_GET(all_items);
	LIST elem;
	
	printf("All items:\n");
	FUNC_LOOP(felem,f) {
	    if (*felem) {
		LIST_LOOP(elem,(LIST)I_GET(*felem)) {
		    printf("\t");
		    printf("0x%x ",L_GET(elem));
		    i_fwrite(ttyout,L_GET(elem));
		    printf("\n");
		}
	    }
	}
}
#endif

#define		NARGS	10

/*******************************************************************************
 * i_deletes - deletes a list of up to 9 items. Care should be taken
 *	not to give it more than 9 items at once (error given). The last item must
 *	always be terminated by (ITEM)I_TERM as the last item.
 */

int
i_deletes(f0,f1,f2,f3,f4,f5,f6,f7,f8,f9)
	ITEM f0,f1,f2,f3,f4,f5,f6,f7,f8,f9;
	{
	ITEM fargs[NARGS],*fptr=fargs;

	*fptr++ = f0; *fptr++ = f1; *fptr++ = f2; *fptr++ = f3; *fptr++ = f4;
	*fptr++ = f5; *fptr++ = f6; *fptr++ = f7; *fptr++ = f8; *fptr = f9;
	for(fptr=fargs;*fptr != (ITEM)I_TERM && ((fptr-fargs) < NARGS);fptr++)
		i_delete(*fptr);
	if ((fptr-fargs) == NARGS)
		d_error("i_deletes - no terminator or too many arguments");
}

/********************************************************************************
 * i_delete - recursively deletes an item of any type.
 */

int
i_delete(i)
	ITEM i;
	{
	register LIST elem;
	register ITEM *felem;
	FUNC f;
#ifdef MEMCHECK
	LIST *hlast;
#endif

	if (i == (ITEM)NULL)	return;
	else if (!(i->usage)) d_error("i_delete - deleting item with no usage");
	else if (--(i->usage) != 0)	return;
	else {
#ifdef MEMCHECK
	    if (*(hlast=h_gen(i,all_items,ADDR))) {
		GOLEM_CFREE(*hlast,sizeof(struct lmem),"i_delete l check");
		*hlast= (*hlast)->next;
	    }
	    else d_error("i_delete - item not found");
#endif
	    switch(i->item_type) {
		case 'i': 	/* Integer */
		case 'v': 	/* Prolog variable */
		case 'h': 	/* Prolog name */
			break;
		case 'b':	/* Block */
			b_delete((BLOCK)I_GET(i));
			break;
		case 'y':	/* Block */
			ar_delete((unsigned long int *)I_GET(i));
			break;
		case 'r':	/* Real number */
			GOLEM_CFREE((POINTER)I_GET(i),
				sizeof(float),"i_delete r");
			break;
		case 'a':	/* Atom */
		case 's':	/* String */
			S_DEL((POINTER)I_GET(i),"i_delete a/s");
			break;
		case 'f':	/* Functor */
			f=(FUNC)I_GET(i);
			FUNC_LOOP(felem,f) {
				i_delete(*felem);
			}
			f_delete(f);
			break;
		case 'l':	/* List */
			LIST_LOOP(elem,(LIST)I_GET(i)) {
				i_delete(L_GET(elem));
				GOLEM_CFREE((POINTER)elem,
					sizeof(struct lmem),"i_delete l");
			}
			break;
		default:
			d_error("i_delete - invalid item type");
	    }
	    GOLEM_CFREE((POINTER)i,sizeof(struct item), "i_delete i");
	}
}

/* ####################################################################### 
 *
 * i_write/3 - writes any item using the generic function put1ch for
 *	writing individual characters. used both for writing to strings
 *	and for writing to files. extra flag decides whether to print
 *	field 'extra'. this is printed in hex between <>s when not unassigned.
 */

int
i_write(i,put1ch,qextra)
	ITEM i;
	LONG (*put1ch) ();
	PREDICATE qextra;
	{
	char c;
	LONG int_cnt,nib_cnt,val;
	float *real;
	char mess[MAXWORD];
	STRING strp;
	LIST elem;
	ITEM *felem;
	FUNC f;
	BLOCK b,bp,bf;

	if (!i) {(*put1ch) ('_'); return;}
	else if (i->usage == 0) d_error("i_fwrite - item with zero usage");
	else {
	    switch(i->item_type) {
		case 'i':	/* Integer */
			sprintf(mess,"%d",(int)I_GET(i));
			STR_LOOP(strp,mess)
				(*put1ch) (*strp);
			break;
		case 'v':	/* Prolog variable */
			sprintf(mess,"@%d",(int)I_GET(i));
			STR_LOOP(strp,mess) (*put1ch) (*strp);
			break;
		case 'b':	/* Block */
			(*put1ch) ('#');
			b=(BLOCK)I_GET(i);
			BLOCK_LOOP(bp,bf,b) {
			  val= *bp;
			  for(nib_cnt=INT_SZ-NBBL_SZ;nib_cnt>=0l;nib_cnt-=NBBL_SZ) {
			    c=val&0xf;
			    (*put1ch) ((c <= 9) ? (c+'0') : (c-10+'A'));
			    val >>= NBBL_SZ;
			  }
			}
			break;
		case 'y':	/* Integer array */
			(*put1ch) ('%');
			Y_DO(bp,i)
			  sprintf(mess,"%d",*bp);
			  STR_LOOP(strp,mess)
				(*put1ch) (*strp);
			  (*put1ch) ('|');
			Y_END
			break;
		case 'r':	/* Float */
			real = (float *)I_GET(i);
			sprintf(mess,"%.2f",*real);
			STR_LOOP(strp,mess) (*put1ch) (*strp);
			break;
		case 'a':	/* Atom */
			STR_LOOP(strp,(STRING)I_GET(i)) (*put1ch) (*strp);
			break;
		case 's':	/* String */
			(*put1ch) ('\'');
			STR_LOOP(strp,(STRING)I_GET(i)) {
				if (*strp == '\'') (*put1ch) ('\\');
				(*put1ch) (*strp);
			}
			(*put1ch) ('\'');
			break;
		case 'h':	/* Prolog name */
			(*put1ch) ('`');
			STR_LOOP(strp,QP_ntos((LONG)I_GET(i))) {
				if (*strp == '`') (*put1ch) ('\\');
				(*put1ch) (*strp);
			}
			(*put1ch) ('`');
			break;
		case 'f':	/* Functor */
			(*put1ch) ('[');
			f=(FUNC)I_GET(i);
			if (f->arr_size) {
				for(felem=f->arr;felem < f->arr+f->arr_size-1;
						felem++) {
					i_write(*felem,put1ch,qextra);
					(*put1ch) (' ');
				}
				i_write(*felem,put1ch,qextra);
			}
			(*put1ch) (']');
			break;
		case 'l':	/* List */
			(*put1ch) ('(');
			if (I_GET(i)) {
				PENL_LOOP(elem,(LIST)I_GET(i)) {
					i_write(L_GET(elem),put1ch,qextra);
					(*put1ch) (' ');
				}
				i_write(L_GET(elem),put1ch,qextra);
			}
			(*put1ch) (')');
			break;
		default:
			d_error("i_write - invalid item type");
	    }
	}
	if(qextra&&i->extra!=UNASS) {
		sprintf(mess,"<%x>",i->extra);
		STR_LOOP(strp,mess) (*put1ch) (*strp);
	}
}

/* ####################################################################### 
 *
 * put1tstring/1 prints the next character to the global string pointer 
 *	it is used by i_write when printing to strings (as opposed to a file).
 */

STRING glob_str;

int
put1tstring(c)
	{
	*glob_str++ = c;
}

int
i_swrite(s,i)
	STRING s;
	ITEM i;
	{
	glob_str = s;
	i_write(i,put1tstring,FALSE);
	put1tstring('\0');
}

FILEREC *glob_file;

/* ####################################################################### 
 *
 * put1tfile/1 prints the next character to the global output file pointer 
 *	it is used by i_write when printing file output (as opposed to strings).
 */

LONG line_cnt;

int
put1tfile1(c)
	register char c;
	{
	*(glob_file->bufp)++ = c;
	if (glob_file->bufp < ((glob_file->buf+LBUF) + BUFSIZE)) return;
	else frecflush(glob_file);
}

int
frecflush(f)
	FILEREC *f;
	{
	register LONG n = (f->bufp - (f->buf+LBUF));
	if (fwrite((f->buf+LBUF),n,1,f->file) != 1)
		printf("frecflush - bad fwrite");
	f->bufp = (f->buf+LBUF);
}

PREDICATE instring,reset=FALSE;

int
put1tfile(c)
	register char c;
	{
	if(!(reset && c==' ')) put1tfile1(c);
	switch(c) {
	    case '\'':
		instring=(instring ? FALSE : TRUE);
		line_cnt++;
		break;
	    case '\n':
		line_cnt=0l;
		break;
	    case '\t':
		line_cnt += 8;
		break;
	    case ' ': case ',': case '|':
		if ((line_cnt++ >= 60) && !instring) {
			put1tfile1('\n');
			put1tfile1('\t');
			line_cnt=8;
			reset=TRUE;
			return;
		}
		break;
	    default:
		line_cnt++;
	}
	reset=FALSE;
}

int
i_fwrite(out,i)
	FILEREC *out;
	ITEM i;
	{
	line_cnt=0l;
	instring=FALSE;
	glob_file=out;
	i_write(i,put1tfile,FALSE);
	frecflush(glob_file);
}

int
i_print(i)
	ITEM i;
	{
	i_fwrite(ttyout,i); printf("\n");
}

int
i_fewrite(out,i)
	FILEREC *out;
	ITEM i;
	{
	line_cnt=0l;
	instring=FALSE;
	glob_file=out;
	i_write(i,put1tfile,TRUE);
	frecflush(glob_file);
}

int
i_fnl(out)
	FILEREC *out;
	{
	glob_file=out;
	put1tfile('\n');
	frecflush(glob_file);
}

int
i_ftab(out)
	FILEREC *out;
	{
	glob_file=out;
	put1tfile('\t');
	frecflush(glob_file);
}

/* ####################################################################### 
 *
 * i_read/2 - reads any item using the generic functions get1ch and unget1ch for
 *	reading individual characters. used both for reading from strings
 *	and for reading from files.
 */

#define		START		0
#define		STR		1
#define		INTGR		2
#define		REAL		3
#define		LIST_ELEM	4
#define		LIST_FIN	5
#define		ATM		6
#define		BLCK		7
#define		FUNC_ELEM	8
#define		FUNC_END	9
#define		VRBL		11
#define		PNAME		12

ITEM
i_read(get1ch,unget1ch)
	char (*get1ch) ();
	LONG (*unget1ch) ();
	{
	register char c;
	char str[MAXMESS];
	STRING strp;
	LONG state=START;
	LONG num,nib_cnt;
	float *real;
	ITEM result,elem,flist;
	LIST *last;
	FUNC f;
	PREDICATE item_started=FALSE;

	while (c = (*get1ch) ()) {
		switch (state) {
		    case START:
			switch (c) {
			    case ' ': case '\t': case '\n': /* White space */
				break;
			    case '%':	/* Comment till end of line */
				while (((*get1ch) ()) != '\n');
				break;
			    case '_':	/* NULL item */
				return((ITEM)NULL);
			    case '\'':	/* Quoted string */
				item_started=TRUE;
				strp=str;
				state=STR;
				break;
			    case '`':	/* Prolog name */
				item_started=TRUE;
				strp=str;
				state=PNAME;
				break;
			    case '-':
			    case '0': case '1': case '2': case '3': case '4':
			    case '5': case '6': case '7': case '8': case '9':
				item_started=TRUE;	/* Integer */
				strp=str;
				*strp++ = c;
				state=INTGR;
				break;
			    case '@':			/* Prolog variable */
				item_started=TRUE;
				strp=str;
				state=VRBL;
				break;
			    case '.':
				item_started=TRUE;	/* Float */
				strp=str;
				*strp++ = c;
				state=REAL;
				break;
			    case '(':			/* List */
				item_started=TRUE;
				result=i_create('l',(POINTER)NULL);
				last = (LIST *)&(result->obj);
				state=LIST_ELEM;
				break;
			    case '[':			/* Functor (array) */
				item_started=TRUE;
				flist=i_create('l',(POINTER)NULL);
				last = (LIST *)&(flist->obj);
				state=FUNC_ELEM;
				break;
			    default:
				if (ALPHA(c)) {		/* Atom */
					item_started=TRUE;
					strp=str;
					*strp++ = c;
					state=ATM;
				}
				else {			/* Error or terminator */
					(*unget1ch) (c);
					return((ITEM)I_TERM);
				}
			}
			break;
		    case PNAME:
			if (c == '\\') *strp++ = (*get1ch) ();
			else if (c == '`') {
				*strp = '\0';
				return(i_create('h',(POINTER)QP_ntos(str,0l)));
			}
			else	*strp++ = c;
			break;
		    case STR:
			if (c == '\\') *strp++ = (*get1ch) ();
			else if (c == '\'') {
				*strp = '\0';
				return(i_create('s',(POINTER)strsave(str)));
			}
			else	*strp++ = c;
			break;
		    case ATM:
			if (ALPHANUM(c))	*strp++ = c;
			else {
				(*unget1ch) (c);
				*strp = '\0';
				return(i_create('a',(POINTER)strsave(str)));
			}
			break;
		    case VRBL:
			switch(c) {
			    case '0': case '1': case '2': case '3': case '4':
			    case '5': case '6': case '7': case '8': case '9':
				*strp++ = c;
				break;
			    default:
				(*unget1ch) (c);
				*strp = '\0';
				sscanf(str,"%ld",&num);
				return(i_create('v',(POINTER)num));
			}
			break;
		    case INTGR:
			switch(c) {
			    case '0': case '1': case '2': case '3': case '4':
			    case '5': case '6': case '7': case '8': case '9':
				*strp++ = c;
				break;
			    case '.': case 'e': case 'E':
				*strp++ = c;
				state = REAL;
				break;
			    default:
				(*unget1ch) (c);
				*strp = '\0';
				sscanf(str,"%ld",&num);
				return(i_create('i',(POINTER)num));
			}
			break;
		    case REAL:
			switch(c) {
			    case '0': case '1': case '2': case '3': case '4':
			    case '5': case '6': case '7': case '8': case '9':
			    case '.': case 'e': case 'E': case '-':
				*strp++ = c;
				break;
			    default:
				(*unget1ch) (c);
				*strp = '\0';
				sscanf(str,"%f",real=r_create(0.0));
				return(i_create('r',(POINTER)real));
			}
			break;
		    case FUNC_ELEM:
			(*unget1ch) (c);
			if ((elem=i_read(get1ch,unget1ch))==(ITEM)I_TERM)
				state=FUNC_END;
			else if (elem==(ITEM)I_ERROR) {
				i_delete(flist);
				return((ITEM)I_ERROR);
			}
			else	last=l_end(elem,last);
			break;
		    case FUNC_END:
			result= f_ltof(flist);
			i_delete(flist);
			if (c == ']') return(result);
			else {
				i_delete(result);
				return((ITEM)I_ERROR);
			}
			break;
		    case LIST_ELEM:
			(*unget1ch) (c);
			if ((elem=i_read(get1ch,unget1ch))==(ITEM)I_TERM) {
				state=LIST_FIN;
			}
			else if (elem==(ITEM)I_ERROR) {
				i_delete(result);
				return((ITEM)I_ERROR);
			}
			else	last=l_end(elem,last);
			break;
		    case LIST_FIN:
			if (c == ')')	return(result);
			else {
				i_delete(result);
				return((ITEM)I_ERROR);
			}
			break;
		    default:
			d_error("i_read - bad state number");
		}
	}
	if (item_started)
		d_error("i_read - unexpected end of input");
	return(i_create('h',(POINTER)peof));
}

/* ####################################################################### 
 *
 * get1fstring/0 gets the next character from the global string buffer 
 *	it is used by i_read when parsing strings (as opposed to a file).
 */

char
get1fstring()
	{
	return(*glob_str++);
}

int
unget1fstring(c)
	char c;		/* Argument not actually used */
	{
	glob_str--;
}

ITEM
i_sread(s)
	STRING s;
	{
	register ITEM result;

	glob_str = s;
	result = i_read(get1fstring,unget1fstring);
	if (result == (ITEM)I_ERROR || result == (ITEM)I_TERM)
		d_error("i_sread - syntax error");
	return(result);
}

/* ####################################################################### 
 *
 * get1ffile/0 gets the next character from the global input file pointer 
 *	it is used by i_read when parsing file input (as opposed to strings).
 */

char
get1ffile1()
	{
	register LONG n;
	if (glob_file->bufp < glob_file->buflim)
		return(*(glob_file->bufp)++);
	else if ((n=fread(glob_file->bufp=glob_file->buf+LBUF,1,
				BUFSIZE,glob_file->file)) > 0) {
		glob_file->buflim=glob_file->bufp+n;
		return(*(glob_file->bufp)++);
	}
	else if (!n) return('\0');
	else d_error("get1ffile - negative value returned by read");
}

char
get1ffile()
	{
	char c;
	if ((c=get1ffile1()) == '\n') (glob_file->line_no)++;
	return(c);
}

int
unget1ffile(c)
	char c;
	{
	if ((*(--(glob_file->bufp))=c) == '\n') (glob_file->line_no)--;
}

char
get1ftty()
	{
	register char c;
	return(((c=getc(stdin)) == EOF) ? '\0' : c);
}

int
unget1ftty(c)
	register char c;
	{
	ungetc(c,stdin);
}

ITEM
i_fread(in)
	FILEREC *in;
	{
	register ITEM result;
	char mess[MAXMESS];

	glob_file = in;
	result = i_read(get1ffile,unget1ffile);
	if (result == (ITEM)I_ERROR || result == (ITEM)I_TERM) {
		sprintf(mess,"i_fread - syntax error at line %ld",glob_file->line_no);
		d_error(mess);
	}
	return(result);
}

ITEM
i_ttyread()
	{
	ITEM result;
	
	result = i_read(get1ftty,unget1ftty);
	if (result == (ITEM)I_ERROR || result == (ITEM)I_TERM) {
		result = (ITEM)I_ERROR;
		while(get1ftty() != '\n');	/* Ignore line */
	}
	return(result);
}

FILEREC *
frecopen(name,mode)
	STRING name,mode;
	{
	FILEREC *result;
	FILE *f=fopen(name,mode);
	if (!f) return((FILEREC *)NULL);
	result=frecreate(name);
	result->file=f;
	return(result);
}

int
freclose(f)
	FILEREC *f;
	{
	fclose(f->file);
	frecdelete(f);
}

FILEREC *
frecreate(name)
	STRING name;
	{
	FILEREC *result;
        if (!(result = (FILEREC *)GOLEM_CALLOC(1l, sizeof(FILEREC), "frecopen"))) {
		d_error("frecopen - calloc failure");
	}
	result->bufp=(result->buflim=result->buf+LBUF);
	result->line_no=1;
	result->filename=strsave(name);
	return(result);
}

int
frecdelete(f)
	FILEREC *f;
	{
	S_DEL(f->filename,"fredelete 1");
	GOLEM_CFREE((POINTER)f,sizeof(FILEREC),"frecdelete 2");
}

/*******************************************************************************
 * i_swap/2 - carries out structural surgery on the objects pointed to
 *	by the two given items. The items must have compatible types.
 *	Returns first argument.
 */

ITEM
i_swap(i1,i2)
	ITEM i1,i2;
	{
	POINTER swapper;
	if (i1->item_type != i2->item_type)
		d_error("i_swap - incompatible item types");
	swapper= i1->obj;
	i1->obj = i2->obj;
	i2->obj = swapper;
	return(i1);
}

/**************************************************************************
 * r_create/0 - returns a pointer to enough space for a floating point
 *	number.
 */

float *
r_create(real)
	float real;
	{
	float *result;

        if (!(result = (float *)GOLEM_CALLOC(1l, sizeof(float), "r_create"))) {
		d_error("r_create - calloc failure");
	}
	*result= real;
	return(result);
}

/*
 * i_tup2/2 - fast version of i_put("[$* $*]",i1,i2)
 */

ITEM
i_tup2(i1,i2)
	ITEM i1,i2;
	{
	FUNC f;
	ITEM result=i_create('f',f=f_create(2l));
	f->arr[0l]=i_inc(i1);
	f->arr[1l]=i_inc(i2);
	return(result);
}

/*
 * i_tup3/3 - fast version of i_put("[$* $* $*]",i1,i2,i3)
 */

ITEM
i_tup3(i1,i2,i3)
	ITEM i1,i2,i3;
	{
	FUNC f;
	ITEM result=i_create('f',f=f_create(3l));
	f->arr[0l]=i_inc(i1);
	f->arr[1l]=i_inc(i2);
	f->arr[2l]=i_inc(i3);
	return(result);
}
