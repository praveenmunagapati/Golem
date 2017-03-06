/* ####################################################################### */

/*                      GOLEM incremental learning control		   */
/*                      ----------------------------------		   */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/* ct_hyp/2 - incremental learning control
 *	Given new example E. Let Es be the set of foreground examples
 *	with the same predicate symbol.
 *	BadEs = EmptySet
 *	DO
 *	  Let Es(n) be a sample of size n from Es-BadEs.
 *	  Let Lggs = {Lgg: E' in Es(n) and Lgg=lgg(E,E',Depth) consistent}.
 *	  Let BadEs \/= {E': E' in Es(n) and lgg(E,E',Depth) inconsistent}.
 *	  Find consistent E' with best cover
 *	  Let E = (E,E')
 *	WHILE increasing-cover
 */

ITEM ct_sample();
ITEM ct_blits();
LONG cl_bcover();

ITEM
ct_hyp(atoms,bestcover,goodEs)
	ITEM atoms;
	LONG bestcover;
	ITEM goodEs;
	{
	ITEM sample,clause,negcov,bposcov,ex1,result,bestatom,
		ex=HOF((LIST)I_GET(atoms));
	LIST elem;
	LONG cover,ncover;
	do {
	  bestatom=(ITEM)NULL; bposcov=(ITEM)NULL;
	  g_message("Pos-neg cover=%ld,potential-examples=%ld",bestcover,b_size(goodEs));
	  sample=ct_sample(ex,exlim,goodEs);
	  LIST_LOOP(elem,(LIST)I_GET(sample)) {
	    clause=ct_blits(l_push(ex1=L_GET(elem),atoms));
	    negcov=cl_subduce(clause,bnegs,smlim);
	    if(debug) {
		g_message("Rlgg of :");
	        cl_showas(ttyout,atoms); printf("  [is]\n");
		cl_fwrite(ttyout,clause); i_fnl(ttyout);
		g_message("Number of negatives covered=%ld",l_length(negcov));
	    }
	    i_dec(l_pop(atoms));
	    if ((ncover=l_length(negcov))<=noiselim) { /* Consistent */
		ITEM newcov;
		g_message("OK");
		if ((cover=(l_length(newcov=cl_subduce(clause,bfores,smlim))-ncover))>bestcover) {
		    i_delete(bposcov);
		    bposcov=newcov;
		    bestatom=ex1;
		    bestcover=cover;
		}
		else i_delete(newcov);
	    }
	    else {
		g_message("Overgeneral");
		b_rem(TNO(ex1->extra),goodEs);
	    }
	    i_deletes(negcov,clause,(ITEM)I_TERM);
	  }
	  if (bestatom) {
		if(debug) {
			printf("[Best-atom ");
			p_fwrite(ttyout,bestatom); printf("]\n");
		}
		l_push(bestatom,atoms);
		ct_rempos(bposcov,goodEs);
		i_delete(bposcov);
	  }
	  i_delete(sample);
	} while(bestatom);
	g_message("Cover=%ld",bestcover);
	result=ct_blits(atoms);
	return(result);
}

/*
 * ct_sample/1 - chooses up to exlim examples from the given list by
 *	taking every length(list)/exlim'th one
 */

ITEM
ct_sample(ex,lim,bits)
	ITEM ex,bits;
	LONG lim;
	{
	ITEM firstarg,result,atoms,bs;
	firstarg=F_ELEM(1,ex);
	result=b_btos(spatoms,bs=b_sample(lim,b_int(bits,F_ELEM(PNO(firstarg->extra),pas))));
	i_delete(bs);
	return(result);
}

/*
 * ct_rempos/2 - removes all atoms corresponding to the given
 *	substitutions from the given atom bitset.
 */

int
ct_rempos(subs,bas)
	ITEM subs,bas;
	{
	register LIST elem;
	LIST_LOOP(elem,(LIST)I_GET(subs))
	    b_rem(TNO(F_ELEM(0l,L_GET(elem))->extra),bas);
}

/*
 * ct_bestpr(*bestcover) - chooses a random sample of pairs of examples
 *	of the target concept and forms their lgg. returns
 *	pair whose lgg has the best coverof those which do not cover any
 *	negatives.
 */

ITEM ct_pairs();

ITEM
ct_bestpr(bestcover,goodEs)
	LONG *bestcover;
	ITEM *goodEs;
	{
	ITEM brand,ex=b_elem(b_first(brand=b_sample(1l,bfores)),spatoms),
		bestpair,pair, firstarg=F_ELEM(1,ex),pairs,clause,
		negcov,poscov, prlggs,lgg,htup,bits=b_int(b_copy(bfores),
		  F_ELEM(PNO(firstarg->extra),pas)),bcov=(ITEM)NULL;
	LIST elem,*last;
	LONG cover,ncover;
	PREDICATE *grnd;
	pairs=ct_pairs(exlim,bits,spatoms);
	bestpair=(ITEM)NULL;
	LIST_LOOP(elem,(LIST)I_GET(pairs)) {
	    clause=ct_blits(pair=L_GET(elem));
	    negcov=cl_subduce(clause,bnegs,smlim);
	    if(debug) {
		g_message("Rlgg of pair:");
	        cl_showas(ttyout,pair); printf("  [is]\n");
		cl_fwrite(ttyout,clause); i_fnl(ttyout);
		g_message("Number of negatives covered=%ld",l_length(negcov));
	    }
	    if ((ncover=l_length(negcov))<=noiselim) { /* Consistent */
		if ((cover=(l_length(poscov=cl_subduce(clause,bfores,smlim))-ncover))> *bestcover) {
		    i_deletes(bestpair,bcov,hypothesis,(ITEM)I_TERM);
		    bestpair=i_inc(pair);
		    bcov=i_inc(poscov);
		    hypothesis=i_inc(clause);
		    *bestcover=cover;
		}
		g_message("Number of positives covered=%ld",l_length(poscov));
		i_delete(poscov);
	    }
	    i_deletes(negcov,clause,(ITEM)I_TERM);
	  }
	  if (bcov) {
		ct_rempos(bcov,*goodEs);
	        i_delete(bcov);
	}
	i_deletes(brand,ex,pairs,bits,(ITEM)I_TERM);
	return(bestpair);
}

LONG b_findnth();
LIST *ct_pairs1();

ITEM
ct_pairs(m,bits,super)
	LONG m;
	ITEM bits,super;
	{
	LONG size; ITEM pairs;
	BLOCK bsum=b_bitsum((BLOCK)I_GET(bits),&size);
	struct otree *tree=ot_sample(m,(size*(size-1))>>1);
	LIST *last=L_LAST(pairs=L_EMPTY);
	ct_pairs1(tree,(BLOCK)I_GET(bits),bsum,size,last);
	b_delete(bsum); ot_delete(tree);
	return(pairs);
}

LIST *
ct_pairs1(tree,b,bsum,size,last)
	struct otree *tree;
	BLOCK b,bsum; LONG size; LIST *last;
	{
	LONG x,y,bitx,bity;
	if(tree) {
		last=ct_pairs1(tree->left,b,bsum,size,last);
		prdecode(tree->val,size,&x,&y);
		bitx=b_findnth(x+1,b,bsum); bity=b_findnth(y+1,b,bsum);
		last=l_end(l_push(i_dec(b_elem(bitx,spatoms)),
		    l_push(i_dec(b_elem(bity,spatoms)),L_EMPTY)),last);
		last=ct_pairs1(tree->right,b,bsum,size,last);
	}
	return(last);
}
