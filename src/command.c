#include <stdio.h>
#include "golem.h"

/*
 * #######################################################################
 *
 *			Command Routines
 *                      ----------------
 *
 * #######################################################################
 */

PREDICATE c_mem();
PREDICATE c_stats();
PREDICATE c_help0();
PREDICATE c_help1();
PREDICATE c_write();
PREDICATE c_read();
PREDICATE c_show();
PREDICATE c_rlgg();
PREDICATE c_construct();
PREDICATE c_set();
PREDICATE c_settings();
PREDICATE c_covers();
PREDICATE c_coversn();
PREDICATE c_subduce();
PREDICATE c_subducen();
PREDICATE c_induce();
PREDICATE c_addhyp();
PREDICATE c_rdhyp();
PREDICATE c_sizes();
PREDICATE c_mode();
PREDICATE c_modes();
PREDICATE c_determination();
PREDICATE c_nondeterminate();
PREDICATE c_debug();
PREDICATE c_sample();
PREDICATE c_randseed();
PREDICATE c_fixedseed();
PREDICATE c_rmcover();
PREDICATE c_op();
extern PREDICATE c_ops();
PREDICATE c_reduce();
PREDICATE c_gen();
PREDICATE c_ypop();
PREDICATE c_ypush();

struct com commands[] = {
	"addhyp", 0l, c_addhyp, "add hypothesis to clause set and remove foreground cover",
	/* "construct", 0l, c_construct, "construct new predicate", */
	"covers", 0l, c_covers, "computes number of foreground examples covered by clause set",
	"coversn", 0l, c_coversn, "computes number of negative examples covered by clause set",
	"debug", 0l, c_debug, "toggle debug information flag",
	"determination", 2l, c_determination, "determination for predicate, eg. determination(mult/3,plus/3)",
	"fixedseed", 0l, c_fixedseed, "initialises random number generator seed to 1",
	"help", 0l, c_help0, "lists commands",
	"help", 1l, c_help1, "gives help information on particular command, eg. help(read/2)",
	"induce", 0l, c_induce, "inductively construct hypothesis from positive examples",
	"mem", 0l, c_mem, "dynamic memory being used by Golem",
	"mode", 1l, c_mode, "mode declaration of predicate, eg. mode(mult(+,+,-))",
	"modes", 0l, c_modes, "show all modes of predicates",
	/* "nondeterminate", 1l, c_nondeterminate, "nondeterminate predicate, eg. nondeterminate(connected/2)", */
	"op", 3l, c_op, "op(Precedence,Associativity,Symbol) same as Prolog",
	"ops", 0l, c_ops, "show present operator precedences and associativities",
	"randseed", 0l, c_randseed, "intitialises random number generator seed using time of day",
	"rdhyp", 0l, c_rdhyp, "read a new hypothesis from stdin",
	"read", 2l, c_read, "read(Type,FileRoot) where Type is one of fore, back, neg, all or rules",
	"reduce", 0l, c_reduce, "reduces the present hypothesis",
	"rlgg", 0l, c_rlgg, "reads atoms from stdin until atom '$'. Takes rlgg of given atoms",
	"rmcover", 0l, c_rmcover, "removes foreground instances covered by rules",
	"sample", 3l, c_sample, "sample(N,file1,file2) random sample of N from file1 to file2",
	"set", 2l, c_set, "set(Limit,IntegerValue) where Limit is one of i, j, noise, rlggsample or testsample",
	"settings", 0l, c_settings, "show present parameter settings",
	"show", 1l, c_show, "show(Type) where Type is one of fore, back, neg, all, rules or hypothesis",
	"sizes", 0l, c_sizes, "displays sizes of foreground, negative, background and clause sets",
	"stats", 0l, c_stats, "table of blocks being used in dynamic memory",
	"subduce", 0l, c_subduce, "computes number of foreground examples covered by hypothesis",
	"subducen", 0l, c_subducen, "computes number of negative examples covered by hypothesis",
	"write", 2l, c_write, "write(Type,FileRoot) where Type is one of fore, back, neg, all or rules",
	/* "ypop", 0l, c_ypop, "insert number into y",
	"ypush", 1l, c_ypush, "insert number into y", */

        0, 0, 0, 0
};


main_prompt()
	{
	ITEM c;
	LONG start;
	char mess[MAXMESS];

	for (;;) {
		printf("!- ");
		if ((c=cl_ttyread(TRUE))==(ITEM)I_ERROR) continue;
		else if (c->item_type == 'h' && (LONG)I_GET(c) ==peof) {
			i_delete(c);
			break;
		}
		l_pop(c);	/* Remove NULL head */
		start=cputime();
		interp_com(c);
		l_push((ITEM)NULL,c);
		cl_swrite(mess,c);
		g_message("%s - Time taken %ldms",mess,cputime()-start);
		i_delete(c);
	}
}

interp_com(comlist)
	ITEM comlist;
	{
	struct com *cptr;
	ITEM command;
	PREDICATE found_com,hasargs;
	LIST elem;
	LONG psym,argsok;
	LIST_LOOP(elem,(LIST)I_GET(comlist)) {
	    found_com=FALSE;
	    command=L_GET(elem);
	    hasargs=(command->item_type == 'f' ?TRUE:FALSE);
	    psym=(hasargs?(LONG)I_GET(F_ELEM(0l,command)):(LONG)I_GET(command));
	    for (cptr=commands;cptr->pattern;cptr++) {
		if (psym==QP_ston(cptr->pattern,cptr->nargs)) {
			found_com=TRUE;
			if(hasargs) argsok=(*(cptr->func))(F_ELEM(1l,command),
						    F_ELEM(2l,command),
						    F_ELEM(3l,command),
						    F_ELEM(4l,command),
						    F_ELEM(5l,command));
			else argsok=(*(cptr->func))();
			break;
		}
	    }
	    if (!found_com || !argsok) {
		if(!found_com) printf("[Bad command - ");
		else printf("[Bad arguments - ");
		p_fwrite(ttyout,command); printf("]\n");
	    }
	}
}

#define CWIDTH 17

PREDICATE
c_help0()
	{
	struct com *cptr;
	LONG cnt1=0,cnt2,columnwidth;
	char mess[MAXMESS];
	printf("The following commands are available:\n\t");
	for (cptr=commands;cptr->pattern;cptr++) {
		sprintf(mess,"%s/%ld",cptr->pattern,cptr->nargs);
		printf(mess);
		for(cnt2=CWIDTH-strlen(mess);cnt2>0;cnt2--)
			printf(" ");
		if (++cnt1 >= 4) {
			cnt1=0l;
			if((cptr+1)->pattern) printf("\n\t");
			else printf("\n");
		}
	}
	if(cnt1) printf("\n");
	return(TRUE);
}


PREDICATE
c_help1(command)
	ITEM command;
	{
	struct com *cptr;
	PREDICATE found_com=FALSE;
	LONG arity;
	STRING name;
	if(fsym(command,&name,&arity)==(LONG)I_ERROR) {
	    printf("[Command should have form help(Command/Arity)]\n");
	    return(TRUE);
	}
	for (cptr=commands;cptr->pattern;cptr++) {
	    if (STREQ(name,cptr->pattern) && arity==cptr->nargs) {
		found_com=TRUE;
		printf("[%s/%ld - %s]\n",cptr->pattern,cptr->nargs,cptr->helpmsg);
		break;
	    }
	}
	if (!found_com) {
	    printf("[Unknown command - %s/%ld]\n",name,arity);
	}
	return(TRUE);
}

PREDICATE
c_mem()
	{
	printf("[%ld bytes in use]\n",memout);
	return(TRUE);
}

PREDICATE
c_stats()
	{
	a_pr_block_stats();
	return(TRUE);
}

PREDICATE
c_write(ftype,name)
	ITEM ftype,name;
	{
	LONG psym;
	if(!(ftype->item_type=='h' && name->item_type=='h'))
		return(FALSE);
	psym=(LONG)I_GET(ftype);
	if(psym==QP_ston("fore",0l)) c_writef(name);
	else if(psym==QP_ston("back",0l)) c_writeb(name);
	else if(psym==QP_ston("neg",0l)) c_writen(name);
	else if(psym==QP_ston("all",0l)) c_writeall(name);
	else if(psym==QP_ston("rules",0l)) c_writerls(name);
	else return(FALSE);
	return(TRUE);
}

PREDICATE
c_writef(fname)
	ITEM fname;
	{
	STRING name;
	ITEM fores=i_sort(b_btos(spatoms,bfores));
	FILEREC *out;
	char file[MAXMESS];
	if(fname->item_type== 'h')
		name=QP_ntos((STRING)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.f",name);
	out=frecopen(file,"w");
	cl_showas(out,fores);
	freclose(out);
	i_delete(fores);
	return(TRUE);
}

PREDICATE
c_writeb(fname)
	ITEM fname;
	{
	STRING name;
	ITEM bbwithoutf,bwithoutf=i_sort(b_btos(spatoms,
		b_sub(bbwithoutf=b_copy(bbacks),bfores)));
	FILEREC *out;
	char file[MAXMESS];
	if(fname->item_type== 'h')
		name=QP_ntos((STRING)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.b",name);
	out=frecopen(file,"w");
	cl_showas(out,bwithoutf);
	freclose(out);
	i_deletes(bbwithoutf,bwithoutf,(ITEM)I_TERM);
	return(TRUE);
}

PREDICATE
c_writen(fname)
	ITEM fname;
	{
	STRING name;
	ITEM negs=i_sort(b_btos(spatoms,bnegs));
	FILEREC *out;
	char file[MAXMESS];
	if(fname->item_type== 'h')
		name=QP_ntos((STRING)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.n",name);
	out=frecopen(file,"w");
	cl_showas(out,negs);
	freclose(out);
	i_delete(negs);
	return(TRUE);
}

PREDICATE
c_writerls(fname)
	ITEM fname;
	{
	STRING name;
	FILEREC *out;
	char file[MAXMESS];
	if(fname->item_type== 'h')
		name=QP_ntos((STRING)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.r",name);
	out=frecopen(file,"w");
	cl_showrls(out,rules);
	freclose(out);
	return(TRUE);
}


PREDICATE
c_writeall(fname)
	ITEM fname;
	{
	c_writef(fname);
	c_writeb(fname);
	c_writen(fname);
	c_writerls(fname);
	return(TRUE);
}

PREDICATE
c_read(ftype,name)
	ITEM ftype,name;
	{
	LONG psym;
	if(!(ftype->item_type=='h' && name->item_type=='h'))
		return(FALSE);
	psym=(LONG)I_GET(ftype);
	if(psym==QP_ston("fore",0l)) c_readf(name);
	else if(psym==QP_ston("back",0l)) c_readb(name);
	else if(psym==QP_ston("neg",0l)) c_readn(name);
	else if(psym==QP_ston("all",0l)) c_readall(name);
	else if(psym==QP_ston("rules",0l)) c_readrls(name);
	else return(FALSE);
	return(TRUE);
}

PREDICATE
c_readall(fname)
	ITEM fname;
	{
	STRING root;
	char file[MAXWORD];
	if(fname->item_type== 'h')
		root=QP_ntos((LONG)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.b",root); cl_readas(file,&bbacks);
	sprintf(file,"%s.f",root); cl_readas(file,&bfores);
	sprintf(file,"%s.n",root); cl_readas(file,&bnegs);
	sprintf(file,"%s.r",root); cl_readrls(file);
	return(TRUE);
}

PREDICATE
c_readf(fname)
	ITEM fname;
	{
	STRING name;
	char file[MAXMESS];
	if(fname->item_type== 'h')
		name=QP_ntos((STRING)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.f",name);
	cl_readas(file,&bfores);
	return(TRUE);
}

PREDICATE
c_readn(fname)
	ITEM fname;
	{
	STRING name;
	char file[MAXMESS];
	if(fname->item_type== 'h')
		name=QP_ntos((STRING)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.n",name);
	cl_readas(file,&bnegs);
	return(TRUE);
}

PREDICATE
c_readb(fname)
	ITEM fname;
	{
	STRING name;
	char file[MAXMESS];
	if(fname->item_type== 'h')
		name=QP_ntos((STRING)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.b",name);
	cl_readas(file,&bbacks);
	return(TRUE);
}

PREDICATE
c_readrls(fname)
	ITEM fname;
	{
	STRING name;
	char file[MAXMESS];
	if(fname->item_type== 'h')
		name=QP_ntos((STRING)I_GET(fname));
	else return(FALSE);
	sprintf(file,"%s.r",name);
	cl_readrls(file);
	return(TRUE);
}

PREDICATE
c_show(stype)
	ITEM stype;
	{
	LONG psym;
	ITEM fores=(ITEM)NULL,backs=(ITEM)NULL,negs=(ITEM)NULL;
	if((stype->item_type!='h')) return(FALSE);
	psym=(LONG)I_GET(stype);
	if(psym==QP_ston("fore",0l)) cl_showas(ttyout,fores=i_sort(b_btos(spatoms,bfores)));
	else if(psym==QP_ston("back",0l)) cl_showas(ttyout,backs=i_sort(b_btos(spatoms,bbacks)));
	else if(psym==QP_ston("neg",0l)) cl_showas(ttyout,negs=i_sort(b_btos(spatoms,bnegs)));
	else if(psym==QP_ston("all",0l)) {
		if(b_size(bfores)>0) {
			printf("[Foreground facts]\n");
			cl_showas(ttyout,fores=i_sort(b_btos(spatoms,bfores)));
		}
		if(b_size(bbacks)>0) {
			printf("[Background facts]\n");
			cl_showas(ttyout,backs=i_sort(b_btos(spatoms,bbacks)));
		}
		if(b_size(bnegs)>0) {
			printf("[Negative facts]\n");
			cl_showas(ttyout,negs=i_sort(b_btos(spatoms,bnegs)));
		}
	}
	else if(psym==QP_ston("rules",0l)) cl_showrls(ttyout,rules);
	else if(psym==QP_ston("hypothesis",0l)) c_showhyp();
	else return(FALSE);
	i_deletes(fores,backs,negs,(ITEM)I_TERM);
	return(TRUE);
}

PREDICATE
c_rlgg()
	{
	LONG pdollar=(LONG)QP_ston("$",0l); /* $/0 */
	LIST elem;
	ITEM tlist,i,atom;
	LIST *last=L_LAST(tlist=L_EMPTY);
	LONG psym= -1,newsym;
	while((i=cl_ttyread(FALSE))==(ITEM)I_ERROR ||
			!(i->item_type == 'h' && (LONG)I_GET(i) ==peof) ) {
	    if(i==(ITEM)I_ERROR) continue;
	    else if(l_length(i)!=1) printf("[Non-unit clause ignored]");
	    else if((atom=HOF((LIST)I_GET(i)))->item_type== 'f')
			newsym=(LONG)I_GET(F_ELEM(0l,atom));
	    else if(atom->item_type== 'h') newsym=(LONG)I_GET(atom);
	    else {
		printf("[Bad atom]\n");
		i_delete(i);
		continue;
	    }
	    if(newsym==pdollar) break;
	    else if (psym== -1 || psym==newsym)
		last=l_end(i_inc(HOF((LIST)I_GET(i))),last);
	    else {
		printf("[Incompatible predicate symbols]\n");
		i_delete(i);
		continue;
	    }
	    psym=newsym;
	    i_delete(i);
	}
	if(L_EMPTYQ(tlist)) {
	  i_deletes(tlist,i,(ITEM)I_TERM);
	  return(FALSE);
	}
	i_deletes(i,hypothesis,(ITEM)I_TERM);
	LIST_LOOP(elem,(LIST)I_GET(tlist))
	  ct_integrate(L_GET(elem));
	hypothesis=ct_blits(tlist);
	cl_fwrite(ttyout,hypothesis); i_fnl(ttyout);
	i_delete(tlist);
	return(TRUE);
}

PREDICATE
c_construct()
	{
	w_control();
	return(TRUE);
}

PREDICATE
c_set(limit,value)
	ITEM limit,value;
	{
	LONG psym,ival;
	if(!(limit->item_type=='h' && value->item_type=='i'))
		return(FALSE);
	psym=(LONG)I_GET(limit);
	ival=(LONG)I_GET(value);
	if(psym==QP_ston("i",0l)) vlim=ival;
	else if(psym==QP_ston("j",0l)) dtlim=ival;
	else if(psym==QP_ston("noise",0l)) noiselim=ival;
	else if(psym==QP_ston("rlggsample",0l)) exlim=ival;
	else if(psym==QP_ston("testsample",0l)) smlim=ival;
	else return(FALSE);
	return(TRUE);
}

PREDICATE
c_settings()
	{
	printf("i=%ld, j=%ld, noise=%ld, rlggsample=%ld, testsample=%ld\n",
		vlim,dtlim,noiselim,exlim,smlim);
	return(TRUE);
}

ITEM cl_subduce();

ITEM
cl_totalcover(bas)
	ITEM bas;
	{
	ITEM substs,result=B_EMPTY,bs1,rule;
	LIST_DO(rule,rules)
		substs=cl_subduce(rule,bas,smlim);
		b_uni(result,bs1=w_extractas(substs));
		i_deletes(substs,bs1,(ITEM)I_TERM);
	LIST_END
	return(result);
}

PREDICATE
c_covers()
	{
	ITEM bs;
	printf("[PosCover = %ld]\n",b_size(bs=cl_totalcover(bfores)));
	i_delete(bs);
	return(TRUE);
}

PREDICATE
c_coversn()
	{
	ITEM bs;
	printf("[NegCover = %ld]\n",b_size(bs=cl_totalcover(bnegs)));
	i_delete(bs);
	return(TRUE);
}

PREDICATE
c_subduce()
	{
	ITEM substs,atoms;
	if (hypothesis) {
	    substs=cl_subduce(hypothesis,bfores,smlim);
	    cl_showas(ttyout,atoms=cl_extractas(substs));
	    printf("[Positive Cover = %ld]\n",l_length(substs));
	    i_deletes(substs,atoms,(ITEM)I_TERM);
	}
	else printf("[Error: no hypothesis]\n");
	return(TRUE);
}

PREDICATE
c_subducen()
	{
	ITEM substs,atoms;
	if (hypothesis) {
	    substs=cl_subduce(hypothesis,bnegs,smlim);
	    cl_showas(ttyout,atoms=cl_extractas(substs));
	    printf("[Negative Cover = %ld]\n",l_length(substs));
	    i_deletes(substs,atoms,(ITEM)I_TERM);
	}
	else printf("[Error: no hypothesis]\n");
	return(TRUE);
}

PREDICATE
c_showhyp()
	{
	if (hypothesis) {
		cl_fwrite(ttyout,hypothesis); i_fnl(ttyout);
	}
	else printf("[There is no hypothesis]\n");
	return(TRUE);
}

ITEM ct_hyp();

PREDICATE
c_addhyp()	/* This was being done with pr_eredundant */
	{
	LONG prenegs=b_size(bnegs),
		prefores=b_size(bfores);
	ITEM bfns=b_uni(b_copy(bfores),bnegs),substs,
		breduns=B_EMPTY;
	LIST elem;
	if (!hypothesis) {
		printf("[WARNING - no present hypothesis]\n");
		i_deletes(bfns,breduns,(ITEM)I_TERM);
		return(TRUE);
	}
	substs=cl_subduce(hypothesis,bfns,smlim);
	LIST_LOOP(elem,(LIST)I_GET(substs)) 
	  b_add(TNO(F_ELEM(0l,L_GET(elem))->extra),breduns);
	i_delete(substs);
	b_sub(bfores,breduns);
	b_sub(bnegs,breduns);
	i_sort(l_push(hypothesis,rules));
	i_delete(hypothesis); hypothesis=(ITEM)NULL;
	g_message("REMOVED: %ld FORES, %ld NEGS",
		prefores-b_size(bfores),prenegs-b_size(bnegs));
	i_deletes(bfns,breduns,(ITEM)I_TERM);
	return(TRUE);
}

PREDICATE
c_rdhyp()
	{
	ITEM clause;
	if ((clause=cl_ttyread(FALSE))!=(ITEM)I_ERROR) {
		i_delete(hypothesis);
		hypothesis=cl_integrate(clause);
	}
	return(TRUE);
}

PREDICATE
c_sizes()
	{
	printf("[FORES: %ld, BACKS: %ld, NEGS: %ld, RULES: %ld]\n",
		b_size(bfores),b_size(bbacks),b_size(bnegs),l_length(rules));
	return(TRUE);
}

extern ITEM ct_bestpr();

PREDICATE
c_induce()
	{
	LONG bestcover=0,total;
	ITEM pair,goodEs=b_copy(bfores);
	if ((b_size(bfores)>=2) && (pair=ct_bestpr(&bestcover,&goodEs))) {
		i_delete(hypothesis);
		hypothesis=ct_hyp(pair,bestcover,goodEs);
		i_delete(pair);
		g_message("Reducing clause");
		c_reduce();
	}
	else printf("[No good hypothesis found]\n");
	i_delete(goodEs);
	return(TRUE);
}

PREDICATE
c_reduce()
	{
	ITEM clauses,best=(ITEM)NULL,clause;
	LIST elem;
	LONG start=cputime(),total,bestsize=MAXMESS,size;
	clauses=cl_ureduce(hypothesis);
	total=cputime()-start;
	LIST_LOOP(elem,(LIST)I_GET(clauses)) {
	    if ((size=l_length(clause=L_GET(elem)))<bestsize) {
	      best=clause;
	      bestsize=size;
	    }
	    cl_fwrite(ttyout,clause); i_fnl(ttyout);
	}
	i_delete(hypothesis);
	hypothesis=i_inc(best);
	i_delete(clauses);
	return(TRUE);
}

PREDICATE
c_mode(pred)
	ITEM pred;
	{
	ITEM pred1=i_copy(pred);
	PREDICATE result=cl_mdeclare(pred1);
	i_delete(pred1);
	return(result);
}

PREDICATE
c_modes()
	{
	FUNC f1=(FUNC)I_GET(modes),f2;
	ITEM *fptr1,mode,rec,*fptr2;
	LONG args;
	FUNC_LOOP(fptr1,f1) {
	  if(*fptr1)
	    LIST_DO(rec,*fptr1)
	      if(!(mode=F_ELEM(1l,rec))) continue;
	      f2=(FUNC)I_GET(mode);
	      printf("  mode(%s(",QP_ntos((LONG)I_GET(FNAME(f2))));
	      args=F_SIZE(mode)-1l;
	      ARG_LOOP(fptr2,f2) {
		if(((LONG)I_GET(*fptr2))==IN) printf("+");
		else printf("-");
		if(--args>0l) printf(",");
	      }
	      printf("))\n");
	    LIST_END
	}
	return(TRUE);
}

PREDICATE
c_determination(pred,subpred)
	ITEM pred,subpred;
	{
	STRING name;
	LONG arity,p,p1;
	ITEM psym,psym1;
	if((p=fsym(pred,&name,&arity))==(LONG)I_ERROR ||
		(p1=fsym(subpred,&name,&arity))==(LONG)I_ERROR) {
	    printf("[Command should have form determination(P1/A1,P2/A2)]\n");
	    return(TRUE);
	}
	cl_ddeclare(psym=i_create('h',(POINTER)p),psym1=i_create('h',(POINTER)p1));
	i_deletes(psym,psym1,(ITEM)I_TERM);
	return(TRUE);
}

PREDICATE
c_nondeterminate(pred)
	ITEM pred;
	{
	STRING name;
	LONG arity,p;
	if (pred->item_type != 'f')
	  return(FALSE);
	else if((p=fsym(pred,&name,&arity))==(LONG)I_ERROR)
	    printf("[Command should have form nondeterminate(Predicate/Arity)]\n");
	else b_add(p,nondeterm);
	return(TRUE);
}

PREDICATE
c_debug()
	{
	if(debug = !debug) printf("[Debugging ON]\n");
	else printf("[Debugging OFF]\n");
	return(TRUE);
}

ITEM
c_rdatoms()
	{
	LONG pdollar=(LONG)QP_ston("$",0l); /* $/0 */
	LIST elem;
	ITEM tlist,i,atom;
	LIST *last=L_LAST(tlist=L_EMPTY);
	LONG psym= -1,newsym;
	while((i=cl_ttyread(FALSE))==(ITEM)I_ERROR ||
			!(i->item_type == 'h' && (LONG)I_GET(i) ==peof) ) {
	    if(i==(ITEM)I_ERROR) continue;
	    else if(l_length(i)!=1) printf("[Non-unit clause ignored]");
	    else if((atom=HOF((LIST)I_GET(i)))->item_type== 'f')
			newsym=(LONG)I_GET(F_ELEM(0l,atom));
	    else if(atom->item_type== 'h') newsym=(LONG)I_GET(atom);
	    else {
		printf("[Bad atom]\n");
		i_delete(i);
		continue;
	    }
	    if(newsym==pdollar) break;
	    else if (psym== -1 || psym==newsym)
		last=l_end(i_inc(HOF((LIST)I_GET(i))),last);
	    else {
		printf("[Incompatible predicate symbols]\n");
		i_delete(i);
		continue;
	    }
	    psym=newsym;
	    i_delete(i);
	}
	i_delete(i);
	return(tlist);
}

PREDICATE
c_doall(froot)
	ITEM froot;
	{
	LONG bestcover=0l,minlc,start,cost;
	ITEM clause,atom,pair,goodEs,clauses,atoms;
	LIST elem;
	char mess[MAXMESS];
	STRING fileroot;
	if(froot==(ITEM)NULL) {
	    printf("[No fileroot given]\n");
	    return(FALSE);
	}
	if(froot->item_type== 'h')
		fileroot=QP_ntos((LONG)I_GET(froot));
	else {
		printf("[Bad file name]\n");
		return(FALSE);
	}
	start=cputime();
	c_readall(froot);
	i_delete(rules); rules=L_EMPTY;
	g_message("Read in %ldms",cputime()-start);
	goodEs=b_copy(bfores);
	start=cputime();
	while ((b_size(bfores)>=2) && (pair=ct_bestpr(&bestcover,&goodEs))) {
		i_delete(hypothesis);
		hypothesis=ct_hyp(pair,bestcover,goodEs);
		g_message("Reducing clause");
		clauses=cl_ureduce(hypothesis);
		i_deletes(pair,hypothesis,(ITEM)I_TERM);
		hypothesis=(ITEM)NULL;
		if (L_EMPTYQ(clauses)) {
		    i_delete(clauses);
		    break;
		}
		LIST_DO(clause,clauses)
		    hypothesis=i_inc(clause);
		    cl_swrite(mess,hypothesis);
		    g_message("Adding clause %s",mess);
		    c_addhyp();
		    if (debug) c_sizes();
		LIST_END
		b_uni(goodEs,bfores);
		bestcover=0l;
		i_delete(clauses);
	}
	g_message("Induction time %ldms",cputime()-start);
	i_delete(goodEs);
	atoms=b_btos(spatoms,bfores);
	LIST_DO(atom,atoms)
	    l_push(i_dec(l_push(atom,L_EMPTY)),rules);
	LIST_END
	i_sort(rules);
	i_delete(atoms);
	c_writerls(froot);
	g_message("Clauses written to %s.r",fileroot);
	return(TRUE);
}

PREDICATE
c_sample(m,file1,file2)
	ITEM m,file1,file2;
	{
	STRING name1,name2;
	FILEREC *in,*out;
	ITEM i;
	LONG mm=(LONG)I_GET(m),nn,r;
	if(file1->item_type== 'h')
		name1=QP_ntos((STRING)I_GET(file1));
	if(file2->item_type== 'h')
		name2=QP_ntos((STRING)I_GET(file2));
	else return(FALSE);
	if (!(in=frecopen(name1,"r"))) {
		printf("[Cannot find %s]\n",name1);
		return(TRUE);
	}
	if (!(out=frecopen(name2,"w"))) {
		printf("[Cannot find %s]\n",name2);
		return(TRUE);
	}
	printf("[Pass 1 - counting input file]\n");
	nn=0l;
	for(;;) {
		i=cl_fread(in,FALSE);
		if(i==(ITEM)I_ERROR) continue;
		else if (i->item_type == 'h' && (LONG)I_GET(i) ==peof) {i_delete(i); break;}
		nn++;
		i_delete(i);
	}
	printf("[Counted %ld clauses]\n",nn);
	freclose(in);
	in=frecopen(name1,"r");
	printf("[Pass 2 - sampling %ld from %ld]\n",mm,nn);
	while(nn > 0) {
		i=cl_fread(in,FALSE);
		if(i==(ITEM)I_ERROR) continue;
		else if (i->item_type == 'h' && (LONG)I_GET(i) ==peof) {i_delete(i); break;}
		if((r=MYRAND(1,nn)) <= mm) {
			cl_fwrite(out,i); i_fnl(out);
			mm--;
		}
		nn--;
		i_delete(i);
	}
	freclose(in); freclose(out);
	return(TRUE);
}

PREDICATE
c_randseed()
	{
	SRAND(datetime());
	printf("[The random number generator has been reset using the time of day]\n");
	return(TRUE);
}

PREDICATE
c_fixedseed()
	{
	SRAND(1);
	printf("[The random number generator has been reset to 1]\n");
	return(TRUE);
}

PREDICATE
c_rmcover()
	{
	LONG prefores=b_size(bfores),prenegs=b_size(bnegs);
	ITEM bcover;
	b_sub(bfores,bcover=cl_totalcover(bfores));
	i_delete(bcover);
	b_sub(bnegs,bcover=cl_totalcover(bnegs));
	i_delete(bcover);
	g_message("REMOVED: %ld FORES, %ld NEGS",
		prefores-b_size(bfores),prenegs-b_size(bnegs));
	return(TRUE);
}

PREDICATE
c_op(prec,assoc,sym)
	ITEM sym,assoc,prec;
	{
	ITEM astring,*entry;
	char mess[MAXWORD];
	LONG psym,passoc;
	if(sym->item_type!='h') return(FALSE);
	else if(assoc->item_type!='h') return(FALSE);
	else if(prec->item_type!='i') return(FALSE);
	psym=(LONG)I_GET(sym);
	passoc=(LONG)I_GET(assoc);
	if(*(entry=f_ins(psym,ops))) {
	    printf("[Redeclaration of operator %s ignored]\n",QP_ntos(psym));
	    return(TRUE);
	}
	astring=i_create('s',strsave(QP_ntos(passoc)));
	*entry=i_tup2(i_dec(astring),prec);
	return(TRUE);
}

PREDICATE
c_ypush(v)
	ITEM v;
	{
	/* *y_ins((LONG)I_GET(n),asz)=(LONG)I_GET(v); */
	Y_PUSH((LONG)I_GET(v),asz);
	i_print(asz);
	printf("ArrSz=%d\n",B_SIZE((BLOCK)I_GET(asz)));
	return(TRUE);
}

PREDICATE
c_ypop()
	{
	printf("%d\n",Y_POP(asz));
	i_print(asz);
	printf("ArrSz=%d\n",B_SIZE((BLOCK)I_GET(asz)));
	return(TRUE);
}
