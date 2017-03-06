/* ####################################################################### */

/*			GOLEM main functions				   */
/*			--------------------				   */

/* ####################################################################### */

#include <stdio.h>
#include "golem.h"

LONG memout;
FILEREC *ttyin;
FILEREC *ttyout;
ITEM varno,spatoms,spsyms,bbacks,rules,ops,asz;
ITEM bfores,bnegs,pts,pas,tps,nondeterm,substats;
ITEM modes,determs,pathio,predatoms,ptas,sppaths,spterms,hypothesis;
LONG exlim,vlim,dtlim,smlim,noiselim,ptno,pdot,pempty,pminus,pplus,pdiv;
LONG pif,pcomma,pdot0;
LONG *hpt[HASH10+1l],peof,charlast;
PREDICATE debug,dostats;

ITEM tag=(ITEM)0xdda38;

/*****************************************************************
 *  c_open/0 - creates and initialises global data structures.
 */

c_open()
	{
	LONG **iptr;
	memout = 0;
	if (memout) printf("Mem out = %ld\n",memout);
	a_zero_table();
#ifdef MEMCHECK
	{
	FUNC f;
	ITEM *fptr;

        all_items = (ITEM)GOLEM_CALLOC(1l, sizeof(struct item), "c_open 1");
	all_items->item_type='f';
	all_items->usage=1;
	if (!(f = (FUNC)GOLEM_CALLOC(1l, sizeof(struct functor), "c_open 2")))
		d_error("c_open - calloc failure 1");
	else if (!(f->arr = (ITEM *)GOLEM_CALLOC(HASH10+1l,sizeof(ITEM),"c_open 3")))
		d_error("c_open - calloc failure 2");
	else
		f->arr_size= HASH10+1l;
	FUNC_LOOP(fptr,f) *fptr=(ITEM)NULL; 
	all_items->obj=(POINTER)f;
	}
#endif
	SRAND(1);
	ttyin=frecreate("stdin"); ttyin->file=stdin;
	ttyout=frecreate("stdout"); ttyout->file=stdout;
	spsyms=b_spcreate(7l);		/* Superset of predicate and function symbols */
	varno=i_create('i',(POINTER)0l);
	pts=i_create('f',(POINTER)f_zero(f_create(512l))); /* Path->terms */
	pas=i_create('f',(POINTER)f_zero(f_create(512l))); /* Path->atoms */
	tps=i_create('f',(POINTER)f_zero(f_create(512l))); /* Term->paths */
	ptas=i_create('f',(POINTER)f_zero(f_create(1024l)));
					/* Path-term to atom bitset mapping */
	pathio=i_create('f',(POINTER)f_zero(f_create(1024l))); /* Path modes */
	ops=i_create('f',(POINTER)f_zero(f_create(64l))); /* Operators */
	modes=h_create(5l);		/* Hash table of IO modes */
	predatoms=i_create('f',(POINTER)f_zero(f_create(32l))); /* Predicate->atom mapping */
	determs=h_create(5l);		/* Hash table of determinations */
	substats=h_create(6l);		/* Hash table of subduction statistics */
	spatoms=b_spcreate(10l);	/* Ground atom bit superset */

	spterms=b_spcreate(10l);	/* Term superset */
	sppaths=b_spcreate(10l);	/* Path superset */
	asz=Y_EMPTY;			/* Atom sizes */
	bbacks=B_EMPTY;			/* Bitset of background atoms */
	bfores=B_EMPTY;			/* Bitset of foreground atoms */
	bnegs=B_EMPTY;			/* Bitset of negative atoms */
	rules=L_EMPTY;			/* Horn clauses rulebase */
	nondeterm=B_EMPTY;		/* Non-determinate predicates */
	hypothesis=(ITEM)NULL;
	vlim=2l; exlim=8l; dtlim=2l; noiselim=0l; smlim=10000l;
	ptno=0l;			/* Path/term number */
	for(iptr=hpt+HASH10+1l;--iptr>=hpt;*iptr=(LONG *)NULL);
	c_initops();			/* Initialise operator precedences */
	pdot=QP_ston(".",2l);		/* ./2 */
	pempty=QP_ston("[]",0l);	/* []/0 */
	pminus=QP_ston("-",0l);		/* -/0 */
	pplus=QP_ston("+",0l);		/* +/0 */
	pif=QP_ston(":-",0l);		/* ':-'/0 */
	pcomma=QP_ston(",",0l);		/* ','/0 */
	pdot0=QP_ston(".",0l);		/* '.'/0 */
	pdiv=QP_ston("/",2l);		/* '/'/2 */
	peof=QP_ston("end_of_file",0l); /* end_of_file/0 */
	debug=TRUE;			/* Debug info flag */
	dostats=TRUE;			/* Stats during clause execution? */
	charlast=SEP;			/* Used for printing Prolog expressions */
}

/*****************************************************************
 *  c_close/0 - deletes global data structures.
 */

c_close()
	{
	LONG **iptr;
	frecdelete(ttyin);
	frecdelete(ttyout);
	i_deletes(fileroot,spsyms,varno,pts,pas,tps,ptas,(ITEM)I_TERM);
	i_deletes(spatoms,sppaths,spterms,bbacks,rules,nondeterm,(ITEM)I_TERM);
	i_deletes(bfores,bnegs,modes,determs,pathio,predatoms,hypothesis,(ITEM)I_TERM);
	i_deletes(substats,ops,asz,(ITEM)I_TERM);
	for(iptr=hpt+HASH10+1l;--iptr>=hpt;)
		if(*iptr) pt_adelete(*iptr);
	spsyms=(ITEM)NULL;
#ifdef MEMCHECK
	{
	FUNC f;
	ITEM *felem;
	LIST elem;

	i_print_all();
	f= (FUNC)I_GET(all_items);
	FUNC_LOOP(felem,f) {
	    if (*felem) {
		while(elem=(LIST)I_GET(*felem)) {
		    (LIST)I_GET(*felem)=elem->next;
		    GOLEM_CFREE(elem,sizeof(struct lmem),"c_close 1");
		}
	        GOLEM_CFREE(*felem,sizeof(struct item),"c_close 2");
	    }
	}
	GOLEM_CFREE(f->arr,(HASH10+1l)*sizeof(ITEM),"c_close 3");
	GOLEM_CFREE(f,sizeof(struct functor),"c_close 4");
	GOLEM_CFREE(all_items,sizeof(struct item), "c_close 5");
	}
#endif
	if (memout) printf("\nMem out = %ld\n",memout);
	else if (interactive) printf("\n");
}

/* c_initops/0 - initialise operator precedences and associativities
 *	This is initialised to all operator settings in Clocksin/Mellish
 *	minus	'.'/2, spy/1 and nospy/1
 *	plus	^/2
 */

struct op_prec {
	STRING operator;
	LONG precedence;
	STRING assoc;
};

struct op_prec prolops[] = {
	":-", 255, "xfx",
	"?-", 255, "fx",
	";", 254, "xfy",
	",", 253, "xfy",
	"not", 60, "fx",
	"is", 40, "xfx",
	"=..", 40, "xfx",
	"=", 40, "xfx",
	"\\=", 40, "xfx",
	"<", 40, "xfx",
	"=<", 40, "xfx",
	">=", 40, "xfx",
	">", 40, "xfx",
	"==", 40, "xfx",
	"\\==", 40, "xfx",
	"-", 31, "yfx",
	"+", 31, "yfx",
	"/", 21, "yfx",
	"*", 21, "yfx",
	"mod", 11, "xfx",
	"^", 10, "xfy",

        0, 0, 0
};

c_initops()
	{
	struct op_prec *optr;
	ITEM *entry,astring;
	LONG psym;
	for (optr=prolops;optr->operator;optr++) {
	  psym=QP_ston(optr->operator,0l);
	  if(*(entry=f_ins(psym,ops))) d_error("c_initops - redeclaration of operator");
	  astring=i_create('s',strsave(optr->assoc));
	  *entry=i_tup2(i_dec(astring),i_dec(I_INT(optr->precedence)));
	}
}

/* c_ops() - prints the present operators' precedences and associativities
 */

PREDICATE
c_ops()
	{
	FUNC f=(FUNC)I_GET(ops);
	ITEM *fptr;
	LONG operator=0l;
	FUNC_LOOP(fptr,f) {
	  if(*fptr) {
	    printf("  op(%d,%s,'%s')\n",(LONG)I_GET(F_ELEM(1l,*fptr)),
		(STRING)I_GET(F_ELEM(0l,*fptr)),QP_ntos(operator));
	  }
	  operator++;
	}
	return(TRUE);
}
