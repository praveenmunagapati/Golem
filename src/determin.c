/* ####################################################################### */

/*                      GOLEM Deterministic Routines                       */
/*                      ----------------------------                       */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/*
 * dt_cross - fast ntuple-determination
     add in determinate literals that share more than
	    2 variables.
	Initialise(VPar,VPar1,IVPar1,last)
	For i=2 to n do
	  ND-npatches=empty-list ; VP1cnt = 0
	  For each var-place VP in VPar
	    Let P=D be 2bitset from last[VP] to size(VPar1)
	    For each atomset As in VPar[VP]   SumAll(P,D,As)
	    Intersect(D,P-D,VPar1,result,ND-npatches,VPCnt)
	    last1[VP] = VP1cnt
	  If i<n then Reinitialise(VPar1,IVPar1,ND-npatches,last,last1)
 */

ITEM b2_allones();

LIST *
dt_cross(apatches,ndeterm,last)
	ITEM apatches;
	PREDICATE ndeterm;
	LIST *last;
	{
	LONG i,VP1cnt,VP,N;
	ITEM VPar,VPar1,IVPar1,NDpatches,*fptr,P,D,vp2sup,
		used;
	unsigned long int *lastvp,*last1vp;
	LIST *lastnd,elem,*lastu; FUNC f;
	PREDICATE cont;
	if(L_EMPTYQ(apatches)) return(last);
	used=B_EMPTY;
	dt_init(apatches,&VPar,&VPar1,&IVPar1,&lastvp);
	for(i=2;i<=dtlim;i++) {
	    cont= (i<dtlim?TRUE:FALSE);
	    lastnd=L_LAST(NDpatches=L_EMPTY); VP=VP1cnt=0l;
	    f=(FUNC)I_GET(VPar); last1vp=ar_create(F_SIZE(VPar));
	    FUNC_LOOP(fptr,f) {
		vp2sup=b2_allones(lastvp[VP+1],F_SIZE(VPar1));
		P=b_copy(D=b_copy(vp2sup)); N=0l;
		LIST_LOOP(elem,(LIST)I_GET(F_ELEM(1,*fptr)))
		    dt_sumall(D,P,vp2sup,N++,L_GET(elem),IVPar1);
		dt_intersect(*fptr,VP,VPar1,D,b_sub(P,D),&last,&lastnd,
			&VP1cnt,used,ndeterm,cont);
		if (cont) {
		    if (VP+1 > *last1vp) ar_enlarge(&last1vp);
		    last1vp[VP+1]=VP1cnt;
		}
		i_deletes(P,D,vp2sup,(ITEM)I_TERM);
		VP++;
	    }
	    if(cont&&VP1cnt)
		dt_reinit(NDpatches,&VPar1,&IVPar1,&lastvp,&last1vp);
	    i_delete(NDpatches); ar_delete(last1vp);
	    if(!VP1cnt) break;
	}
	i_deletes(VPar,VPar1,IVPar1,used,(ITEM)I_TERM); ar_delete(lastvp);
	return(last);
}


ITEM dt_inverse();

dt_init(apatches,VPar,VPar1,IVPar1,lastvp)
	ITEM apatches,*VPar,*VPar1,*IVPar1;
	unsigned long int **lastvp;
	{
	register LIST elem;
	register unsigned long int VP=0,*arp,*arend;
	ITEM *arrp,pair;
	*VPar=i_inc(*VPar1=i_create('f',f_create(l_length(apatches))));
	arrp=((FUNC)I_GET(*VPar))->arr;
	LIST_LOOP(elem,(LIST)I_GET(apatches)) {
	    *arrp++ =pair=i_tup2(i_dec(b_add(VP++,B_EMPTY)),L_GET(elem));
	}
	*IVPar1=dt_inverse(*VPar1);
	*lastvp=ar_create(F_SIZE(*VPar)); VP=0l;
	AR_LOOP(arp,arend,*lastvp) *arp= ++VP;
}

/*
 * dt_inverse/1 - make atom-number to var-place mapping. This
 *	creates a 2D array of 2bit sets.
 */

ITEM
dt_inverse(VPar)
	ITEM VPar;
	{
	register LONG ntup=l_length(F_ELEM(1,F_ELEM(0,VPar))),vpno=0,tupno;
	register ITEM result=i_create('f',f_zero(f_create(
		(LONG)I_GET(F_ELEM(2,spatoms))))),*fptr;
	register LIST elem;
	register FUNC f=(FUNC)I_GET(VPar);
	FUNC_LOOP(fptr,f) {
	    tupno=0l;
	    LIST_LOOP(elem,(LIST)I_GET(F_ELEM(1,*fptr)))
		dt_inverse1(L_GET(elem),tupno++,ntup,vpno,result);
	    vpno++;
	}
	return(result);
}

dt_inverse1(as,tupno,ntup,vpno,inverse)
	ITEM as,inverse;
	LONG tupno,vpno;
	{
	register ITEM *sarr=((FUNC)I_GET(inverse))->arr,*fptr;
	register FUNC f;
	BIT_DO(sarr,as)
	      if (!(*sarr)) {
		*sarr=i_create('f',(POINTER)(f=f_create(ntup)));
	        FUNC_LOOP(fptr,f) *fptr=i_create('b',
			(POINTER)b_create(vpno>>LOG_INT_SZ));
	      }
	      b_add(vpno<<1,F_ELEM(tupno,*sarr));
	BIT_END
}

/*
 * b2_allones - create a 2bit set containing bits set from start
 *	to finish. 2bit sets have only the first bit in every 2 set.
 */

#define	LOMASK	0x55555555
#define	HIMASK	0xaaaaaaaa

ITEM 
b2_allones(start,finish)
	register LONG start,finish;
	{
	ITEM result=i_create('b',(POINTER)b_create((finish>>(LOG_INT_SZ-1))+2));
	BLOCK b=(BLOCK)I_GET(result);
	register BLOCK bp,bend;
	register LONG dec=INT_SZ>>1;
	PREDICATE started=FALSE;
	BLOCK_LOOP(bp,bend,b) {
	    if (started) *bp=LOMASK;
	    else if (start>=dec) {*bp=0l; start-=dec;}
	    else {*bp=LOMASK<<(start<<1); started=TRUE;}
	}
	return(result);
}

/* dt_sumall/6 - does a binary 2bit sum of all the vp2sets in
 *	inverse corresponding to the atoms as and tuple number
 *	N.
  SumAll(P,D)
	D1=Binary2bit-Sum of IVpar1 for all Atoms in VPar[VP,2,N]
	P1=One-or-more(D1)
	D = D /\ D1
	P = P /\ P1
 */

ITEM b2_sum(),b2_1ormore();

dt_sumall(D,P,vp2sup,N,as,IVPar1)
	ITEM D,P,vp2sup,as,IVPar1;
	LONG N;
	{
	register ITEM *sarr=((FUNC)I_GET(IVPar1))->arr,
		vp2sum=B_EMPTY;
	BIT_DO(sarr,as)
	    if(*sarr) b2_sum(vp2sum,b_int(F_ELEM(N,*sarr),vp2sup));
	BIT_END
	b_int(D,vp2sum);
	b_int(P,b2_1ormore(vp2sum));
	i_delete(vp2sum);
}

/*
 * b2_sum/2 - destructively takes 2bit sum, overwriting
 *	and returning first argument. This is stored as
 *	rows of 2 bit sums, i.e. 16 2-bit sums per
 *	32 bit word. Each 2 bit cell is allowed to have one of 3 states.
 *
 *	00 - 0 sum
 *	01 - 1 sum
 *	10 - more than 1
 *
 *	The second argument of the sum can only have cells using the
 *	first 2 states, i.e. it is a "stretched" bitset. These two
 *	are added together as unsigned ints and then the high bit
 *	is used to modify the low bit so that 11 becomes 10. This
 *	requires the boolean function
 *
 *		 Lo 0 1
 *		Hi\____
 *		0 | 0 1
 *		1 | 0 0
 *
 *	which is ~Hi /\ Lo. The function
 *	can be implemented as a parallel operation as follows.
 *
 *	bsum(Sum,Bset) :
 *		Sum &= (((Sum + Bset) ^ HiMask) >> 1) | HiMask
 *
 *	eg. let Sum  = 01 00 10 01 00 10
 *		Bset = 01 00 01 00 01 00
 *		Sum' = 10 00 11 01 01 10
 *		XOR  = 00 10 01 11 11 00
 *		>>   = 00 01 00 11 11 10
 *		OR   = 10 11 10 11 11 10
 *		Sum''= 10 00 10 01 01 10
 */

extern BLOCK b_copy1();

ITEM
b2_sum(bs1,bs2)
	ITEM bs1,bs2;
	{
	register BLOCK bp1,bp2,bf1,bf2,b1=(BLOCK)I_GET(bs1),
		b2=(BLOCK)I_GET(bs2),newb;
	if (B_SIZE(b1) < B_SIZE(b2)) {
		newb=b_copy1(b_create(B_SIZE(b2)-1),b1);
		b_delete(b1);
		(BLOCK)I_GET(bs1)=(b1=newb);
	}
	BLOCK_LOOP2(bp1,bp2,bf1,bf2,b1,b2) {
		*bp1 += *bp2;
		*bp1&= ((*bp1^HIMASK)>>1)|HIMASK;
	}
	return(bs1);
}

/*
 * b2_1ormore - destructively creates a 2bitset in which
 *	for every place low bit is set in result if either
 *	high or low bit set in input.
 */

ITEM 
b2_1ormore(bs)
	ITEM bs;
	{
	BLOCK b=(BLOCK)I_GET(bs);
	register BLOCK bp,bend;
	BLOCK_LOOP(bp,bend,b) *bp= ((*bp>>1)| *bp)&LOMASK;
	return(bs);
}

/* dt_intersect/8 -
   Intersect(D,P,result,ND-npatches,VPCnt)
	For each VP1 in D
	    Add deterministic literal constructed by
		intersecting VP and VP1 to result
	For each VP1 in P
	    If VP not in VPar1[VP1,1] then
		  Add <VP\/VPar1[VP1,1],VPar[VP,2]/\VPar1[VP1,2]> to ND-npatches
		  VPcnt++
 */

dt_intersect(pair,VP,VPar1,D,P,last,lastnd,VP1cnt,used,ndeterm,cont)
	ITEM pair,D,P,VPar1,used;
	LIST **last,**lastnd;
	LONG VP,*VP1cnt;
	PREDICATE ndeterm,cont;
	{
	register LIST elem1,elem2,*last1;
	ITEM tuple=F_ELEM(1l,pair),tuple2,pair1,pair2,vars;
	register LONG index=0l;
	if(!b_emptyq(D)) {
	  BIT_DO(index,D)
	    pair1=F_ELEM(index>>1,VPar1);
	    last1=L_LAST(tuple2=L_EMPTY);
	    LIST_LOOP2(elem1,elem2,(LIST)I_GET(tuple),
	 	(LIST)I_GET(F_ELEM(1l,pair1)))
	      last1=l_end(b_int(b_copy(L_GET(elem1)),L_GET(elem2)),last1);
	    *last=l_end(tuple2,*last);
	  BIT_END
	}
	if (cont || ndeterm) {
	    index=0l;
	    BIT_DO(index,P)
	        pair1=F_ELEM(index>>1,VPar1);
		last1=L_LAST(tuple2=L_EMPTY);
		LIST_LOOP2(elem1,elem2,(LIST)I_GET(tuple),
		    (LIST)I_GET(F_ELEM(1,pair1)))
		  last1=l_end(b_int(b_copy(L_GET(elem1)),L_GET(elem2)),last1);
		if(ndeterm) *last=l_end(i_inc(tuple2),*last);
		pair2=i_tup2(i_dec(b_uni(b_copy(F_ELEM(0l,pair1)),
			F_ELEM(0l,pair))),i_dec(tuple2));
		*lastnd=l_end(pair2,*lastnd);
		(*VP1cnt)++;
	    BIT_END
	}
}

/* dt_reinit/5
  Reinitialise(VPar1,IVPar1,ND-npatches,last,last1)
	Let VPar1 = Array(ND-npatches)
	Let IVPar1 = inverse(Vpar1)
	swap(last,last1)
 */

dt_reinit(NDpatches,VPar1,IVPar1,lastvp,last1vp)
	ITEM NDpatches,*VPar1,*IVPar1;
	unsigned long int **lastvp,**last1vp;
	{
	unsigned long int *swap;
	i_deletes(*VPar1,*IVPar1,(ITEM)I_TERM);
	*VPar1=f_ltof(NDpatches);
	*IVPar1=dt_inverse(*VPar1);
	swap= *lastvp; *lastvp= *last1vp; *last1vp=swap;
}
