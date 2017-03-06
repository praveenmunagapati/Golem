/* ####################################################################### */

/*                      GOLEM random sampling				   */
/*                      ---------------------				   */

/* ####################################################################### */

#include        <stdio.h>
#include	"golem.h"


/*
 * hibit/1 - finds the highest bit set in an integer by binary chop.
 *	Fails when given 0.
 */

LONG
hibit(n)
	register unsigned long int n;
	{
	register long int hi=INT_SZ-1,lo=0,mid;
	if (!n) d_error("hibit - given 0 as input");
	while (hi != lo) {
		mid=((hi-lo)>>1)+lo;
		if (!(n>>(mid+1))) hi=mid;
		else lo=mid+1;
	}
	return(hi);
}

/*
 * b_smpair/3 - efficient method for picking a random pair <x,y>
 *	where both x and y are in the range 0 to sz-1 and
 *	x<y.
 */

b_smpair(sz,x,y)
	LONG sz,*x,*y;
	{
	LONG val,swap;
	if(sz<2) d_error("b_smpair - set size < 2");
	val=MYRAND(0,sz*(sz-1));
	if((*x=val/sz)>=(*y=val%sz)) {
	  swap= *y;
	  *y= *x+1;
	  *x= swap;
	}
}


LONG
isqrt(sq)
	LONG sq;
	{
	LONG oldi,newi;
	float oldf,newf,sqf=sq;
	if(sq==0) return(0);
	else if(sq<0) d_error("isqrt - negative argument");
	newi=1<<(hibit(sq)>>1); newf=newi;
	do {
	  oldf=newf;
	  newf=(oldf+sqf/oldf)/2;
	  oldi=oldf; newi=newf;
	} while(oldi!=newi);
	return(newi);
}

/*
 * prencode/3 - given 0<=x<y<n this function encodes the
 *	pair <x,y> to a unique number in the range [1,n*(n-1)/2]
 *	The result k= x((2n-3)-x)/2 + y
 */

LONG
prencode(x,y,n)
	LONG x,y,n;
	{
	if(n>30000) d_error("prencode - set too large");
	else if(x<0||y<=x||n<=y) d_error("prencode - bad values");
	return(((x*((n<<1)-3-x))>>1)+y);
}

/*
 * prdecode/4 - given k=prencode(x,y,n) this function decodes
 *	x and y from k and n. Decoding is done by binary
 *	chop. Upper and lower bounds are computed using
 *	(2n-3-sqrt(abs((2n-3)^2-8k+8(n-1))))/2 <=x<=
 *		(2n-3-sqrt(abs((2n-3)^2-8k+8)))/2. y is
 *	computed using y=(x(x-(2n-3))+2k)/2
 */

prdecode(k,n,x,y)
	LONG k,n,*x,*y;
	{
	LONG lo,hi,mid,n2=(n<<1)-3,k2=k<<1,sq=(n2*n2)-(k<<3);
	if(n>30000) d_error("prdecode - set too large");
	else if(k<=0||k>(n*(n-1))>>1) d_error("prdecode - bad values");
	lo=(n2-isqrt(sq+((n-1)<<3)))>>1;
	hi=sq+8>0?(n2-isqrt(sq+8))>>1:n2>>1;
	do {
		mid=((hi-lo)>>1)+lo;
		*y=(mid*(mid-n2)+k2)>>1;
		if(*y<=mid) hi=mid;
		else if(*y<n) {lo=mid;break;}
		else lo=mid+1;
	} while (hi>lo);
	*x=lo;
	*y=(lo*(lo-n2)+k2)>>1;
}

struct otree *
ot_create(v,nl)
	LONG v,nl;
	{
	struct otree *result;
	if (!(result = (struct otree *)GOLEM_CALLOC(1, sizeof(struct otree), "ot_create")))
		d_error("ot_create - calloc failure");
	result->val=v;
	result->nleft=nl;
	result->left=(struct otree *)NULL;
	result->right=(struct otree *)NULL;
	return(result);
}

ot_delete(o)
	struct otree *o;
	{
	if(!o) return;
	ot_delete(o->left);
	ot_delete(o->right);
	GOLEM_CFREE(o,sizeof(struct otree),"ot_delete");
}

struct otree *
ot_ins(v,lo,tree)
	LONG v,lo;
	struct otree *tree;
	{
	struct otree **ptree= &tree;
	while(*ptree)
	    if(v<= (*ptree)->nleft) {(*ptree)->nleft--;ptree= &((*ptree)->left);}
	    else {v-=(*ptree)->nleft;lo=(*ptree)->val;ptree= &((*ptree)->right);}
	*ptree=ot_create(v+lo,v-1);
	return(tree);
}

ot_print(indent,tree)
	LONG indent;
	struct otree *tree;
	{
	LONG cnt;
	if(tree) {
		ot_print(indent+1,tree->left);
		for(cnt=indent;cnt>0;cnt--) printf("    ");
		printf("<%d,%d>\n",tree->val,tree->nleft);
		ot_print(indent+1,tree->right);
	}
	else {
		for(cnt=indent;cnt>0;cnt--) printf("    ");
		printf("_\n");
	}
}

/*
 * ot_sample(m,n,tree) - randomly choose m different pairs from
 *	a set size n and insert into tree. Return tree.
 */

struct otree *
ot_sample(m,n)
	LONG m,n;
	{
	struct otree *tree=(struct otree *)NULL;
	if(m>n) m=n;
	for(;m>0;m--,n--) tree=ot_ins(MYRAND(1,n),0,tree);
	return(tree);
}

ot_prprint(tree,n)
	struct otree *tree;
	LONG n;
	{
	LONG x,y;
	if(tree) {
		ot_prprint(tree->left,n);
		prdecode(tree->val,n,&x,&y);
		printf("<%d,%d>\n",x,y);
		ot_prprint(tree->right,n);
	}
}

/*
 * b_bitsum/2 - returns an array giving for each word in the bitset the sum of the
 *	number of bits up to that word.
 */

BLOCK
b_bitsum(b1,total)
	BLOCK b1;
	LONG *total;
	{
	register LONG cnt,sum=0l;
	register unsigned long int val;
	register BLOCK bp1,be1,b2=b_create(B_SIZE(b1)),bp2,be2;
	BLOCK_LOOP2(bp1,bp2,be1,be2,b1,b2) {
	  *bp2=sum;
	  if (val= *bp1)
	    for (cnt=0l;cnt<INT_SZ;cnt+=BYTE_SZ,val>>=BYTE_SZ)
	      sum += byte_sz[val&0xff];
	}
	*total=sum;
	return(b2);
}

/*
 * b_samprem/4 - carries out a binary split search for the
 *	integer containing the given element and returns
 *	the bit number.
 */

LONG w_findnth();

LONG
b_findnth(elem,b,bitsum)
	LONG elem;
	BLOCK b,bitsum;
	{
	register LONG lo,hi,mid,nleft,word;
	hi=B_SIZE(b)-1; b++; bitsum++;
	for(lo=0l;lo<hi;) {
	  mid=lo+(((hi-lo)+1)>>1);
	  if (elem<=bitsum[mid]) hi=mid-1;
	  else lo=mid;
	}
	return((lo<<LOG_INT_SZ)+w_findnth(elem-bitsum[lo],b[lo]));
}

/*
 * bitsinc is a table indicating the position of bits that are set
 *	in a byte. The nth bit which is set in i is bit number
 *	bitsinc[i][n-1].
 */

LONG bitsinc[BYTE_RNG] [BYTE_SZ] =
{{8,8,8,8,8,8,8,8},{0,8,8,8,8,8,8,8},{1,8,8,8,8,8,8,8},{0,1,8,8,8,8,8,8},
 {2,8,8,8,8,8,8,8},{0,2,8,8,8,8,8,8},{1,2,8,8,8,8,8,8},{0,1,2,8,8,8,8,8},
 {3,8,8,8,8,8,8,8},{0,3,8,8,8,8,8,8},{1,3,8,8,8,8,8,8},{0,1,3,8,8,8,8,8},
 {2,3,8,8,8,8,8,8},{0,2,3,8,8,8,8,8},{1,2,3,8,8,8,8,8},{0,1,2,3,8,8,8,8},
 {4,8,8,8,8,8,8,8},{0,4,8,8,8,8,8,8},{1,4,8,8,8,8,8,8},{0,1,4,8,8,8,8,8},
 {2,4,8,8,8,8,8,8},{0,2,4,8,8,8,8,8},{1,2,4,8,8,8,8,8},{0,1,2,4,8,8,8,8},
 {3,4,8,8,8,8,8,8},{0,3,4,8,8,8,8,8},{1,3,4,8,8,8,8,8},{0,1,3,4,8,8,8,8},
 {2,3,4,8,8,8,8,8},{0,2,3,4,8,8,8,8},{1,2,3,4,8,8,8,8},{0,1,2,3,4,8,8,8},
 {5,8,8,8,8,8,8,8},{0,5,8,8,8,8,8,8},{1,5,8,8,8,8,8,8},{0,1,5,8,8,8,8,8},
 {2,5,8,8,8,8,8,8},{0,2,5,8,8,8,8,8},{1,2,5,8,8,8,8,8},{0,1,2,5,8,8,8,8},
 {3,5,8,8,8,8,8,8},{0,3,5,8,8,8,8,8},{1,3,5,8,8,8,8,8},{0,1,3,5,8,8,8,8},
 {2,3,5,8,8,8,8,8},{0,2,3,5,8,8,8,8},{1,2,3,5,8,8,8,8},{0,1,2,3,5,8,8,8},
 {4,5,8,8,8,8,8,8},{0,4,5,8,8,8,8,8},{1,4,5,8,8,8,8,8},{0,1,4,5,8,8,8,8},
 {2,4,5,8,8,8,8,8},{0,2,4,5,8,8,8,8},{1,2,4,5,8,8,8,8},{0,1,2,4,5,8,8,8},
 {3,4,5,8,8,8,8,8},{0,3,4,5,8,8,8,8},{1,3,4,5,8,8,8,8},{0,1,3,4,5,8,8,8},
 {2,3,4,5,8,8,8,8},{0,2,3,4,5,8,8,8},{1,2,3,4,5,8,8,8},{0,1,2,3,4,5,8,8},
 {6,8,8,8,8,8,8,8},{0,6,8,8,8,8,8,8},{1,6,8,8,8,8,8,8},{0,1,6,8,8,8,8,8},
 {2,6,8,8,8,8,8,8},{0,2,6,8,8,8,8,8},{1,2,6,8,8,8,8,8},{0,1,2,6,8,8,8,8},
 {3,6,8,8,8,8,8,8},{0,3,6,8,8,8,8,8},{1,3,6,8,8,8,8,8},{0,1,3,6,8,8,8,8},
 {2,3,6,8,8,8,8,8},{0,2,3,6,8,8,8,8},{1,2,3,6,8,8,8,8},{0,1,2,3,6,8,8,8},
 {4,6,8,8,8,8,8,8},{0,4,6,8,8,8,8,8},{1,4,6,8,8,8,8,8},{0,1,4,6,8,8,8,8},
 {2,4,6,8,8,8,8,8},{0,2,4,6,8,8,8,8},{1,2,4,6,8,8,8,8},{0,1,2,4,6,8,8,8},
 {3,4,6,8,8,8,8,8},{0,3,4,6,8,8,8,8},{1,3,4,6,8,8,8,8},{0,1,3,4,6,8,8,8},
 {2,3,4,6,8,8,8,8},{0,2,3,4,6,8,8,8},{1,2,3,4,6,8,8,8},{0,1,2,3,4,6,8,8},
 {5,6,8,8,8,8,8,8},{0,5,6,8,8,8,8,8},{1,5,6,8,8,8,8,8},{0,1,5,6,8,8,8,8},
 {2,5,6,8,8,8,8,8},{0,2,5,6,8,8,8,8},{1,2,5,6,8,8,8,8},{0,1,2,5,6,8,8,8},
 {3,5,6,8,8,8,8,8},{0,3,5,6,8,8,8,8},{1,3,5,6,8,8,8,8},{0,1,3,5,6,8,8,8},
 {2,3,5,6,8,8,8,8},{0,2,3,5,6,8,8,8},{1,2,3,5,6,8,8,8},{0,1,2,3,5,6,8,8},
 {4,5,6,8,8,8,8,8},{0,4,5,6,8,8,8,8},{1,4,5,6,8,8,8,8},{0,1,4,5,6,8,8,8},
 {2,4,5,6,8,8,8,8},{0,2,4,5,6,8,8,8},{1,2,4,5,6,8,8,8},{0,1,2,4,5,6,8,8},
 {3,4,5,6,8,8,8,8},{0,3,4,5,6,8,8,8},{1,3,4,5,6,8,8,8},{0,1,3,4,5,6,8,8},
 {2,3,4,5,6,8,8,8},{0,2,3,4,5,6,8,8},{1,2,3,4,5,6,8,8},{0,1,2,3,4,5,6,8},
 {7,8,8,8,8,8,8,8},{0,7,8,8,8,8,8,8},{1,7,8,8,8,8,8,8},{0,1,7,8,8,8,8,8},
 {2,7,8,8,8,8,8,8},{0,2,7,8,8,8,8,8},{1,2,7,8,8,8,8,8},{0,1,2,7,8,8,8,8},
 {3,7,8,8,8,8,8,8},{0,3,7,8,8,8,8,8},{1,3,7,8,8,8,8,8},{0,1,3,7,8,8,8,8},
 {2,3,7,8,8,8,8,8},{0,2,3,7,8,8,8,8},{1,2,3,7,8,8,8,8},{0,1,2,3,7,8,8,8},
 {4,7,8,8,8,8,8,8},{0,4,7,8,8,8,8,8},{1,4,7,8,8,8,8,8},{0,1,4,7,8,8,8,8},
 {2,4,7,8,8,8,8,8},{0,2,4,7,8,8,8,8},{1,2,4,7,8,8,8,8},{0,1,2,4,7,8,8,8},
 {3,4,7,8,8,8,8,8},{0,3,4,7,8,8,8,8},{1,3,4,7,8,8,8,8},{0,1,3,4,7,8,8,8},
 {2,3,4,7,8,8,8,8},{0,2,3,4,7,8,8,8},{1,2,3,4,7,8,8,8},{0,1,2,3,4,7,8,8},
 {5,7,8,8,8,8,8,8},{0,5,7,8,8,8,8,8},{1,5,7,8,8,8,8,8},{0,1,5,7,8,8,8,8},
 {2,5,7,8,8,8,8,8},{0,2,5,7,8,8,8,8},{1,2,5,7,8,8,8,8},{0,1,2,5,7,8,8,8},
 {3,5,7,8,8,8,8,8},{0,3,5,7,8,8,8,8},{1,3,5,7,8,8,8,8},{0,1,3,5,7,8,8,8},
 {2,3,5,7,8,8,8,8},{0,2,3,5,7,8,8,8},{1,2,3,5,7,8,8,8},{0,1,2,3,5,7,8,8},
 {4,5,7,8,8,8,8,8},{0,4,5,7,8,8,8,8},{1,4,5,7,8,8,8,8},{0,1,4,5,7,8,8,8},
 {2,4,5,7,8,8,8,8},{0,2,4,5,7,8,8,8},{1,2,4,5,7,8,8,8},{0,1,2,4,5,7,8,8},
 {3,4,5,7,8,8,8,8},{0,3,4,5,7,8,8,8},{1,3,4,5,7,8,8,8},{0,1,3,4,5,7,8,8},
 {2,3,4,5,7,8,8,8},{0,2,3,4,5,7,8,8},{1,2,3,4,5,7,8,8},{0,1,2,3,4,5,7,8},
 {6,7,8,8,8,8,8,8},{0,6,7,8,8,8,8,8},{1,6,7,8,8,8,8,8},{0,1,6,7,8,8,8,8},
 {2,6,7,8,8,8,8,8},{0,2,6,7,8,8,8,8},{1,2,6,7,8,8,8,8},{0,1,2,6,7,8,8,8},
 {3,6,7,8,8,8,8,8},{0,3,6,7,8,8,8,8},{1,3,6,7,8,8,8,8},{0,1,3,6,7,8,8,8},
 {2,3,6,7,8,8,8,8},{0,2,3,6,7,8,8,8},{1,2,3,6,7,8,8,8},{0,1,2,3,6,7,8,8},
 {4,6,7,8,8,8,8,8},{0,4,6,7,8,8,8,8},{1,4,6,7,8,8,8,8},{0,1,4,6,7,8,8,8},
 {2,4,6,7,8,8,8,8},{0,2,4,6,7,8,8,8},{1,2,4,6,7,8,8,8},{0,1,2,4,6,7,8,8},
 {3,4,6,7,8,8,8,8},{0,3,4,6,7,8,8,8},{1,3,4,6,7,8,8,8},{0,1,3,4,6,7,8,8},
 {2,3,4,6,7,8,8,8},{0,2,3,4,6,7,8,8},{1,2,3,4,6,7,8,8},{0,1,2,3,4,6,7,8},
 {5,6,7,8,8,8,8,8},{0,5,6,7,8,8,8,8},{1,5,6,7,8,8,8,8},{0,1,5,6,7,8,8,8},
 {2,5,6,7,8,8,8,8},{0,2,5,6,7,8,8,8},{1,2,5,6,7,8,8,8},{0,1,2,5,6,7,8,8},
 {3,5,6,7,8,8,8,8},{0,3,5,6,7,8,8,8},{1,3,5,6,7,8,8,8},{0,1,3,5,6,7,8,8},
 {2,3,5,6,7,8,8,8},{0,2,3,5,6,7,8,8},{1,2,3,5,6,7,8,8},{0,1,2,3,5,6,7,8},
 {4,5,6,7,8,8,8,8},{0,4,5,6,7,8,8,8},{1,4,5,6,7,8,8,8},{0,1,4,5,6,7,8,8},
 {2,4,5,6,7,8,8,8},{0,2,4,5,6,7,8,8},{1,2,4,5,6,7,8,8},{0,1,2,4,5,6,7,8},
 {3,4,5,6,7,8,8,8},{0,3,4,5,6,7,8,8},{1,3,4,5,6,7,8,8},{0,1,3,4,5,6,7,8},
 {2,3,4,5,6,7,8,8},{0,2,3,4,5,6,7,8},{1,2,3,4,5,6,7,8},{0,1,2,3,4,5,6,7}};

/*
 * w_findnth/2 - find the nth bit set in the word and return its bit number.
 */

LONG
w_findnth(n,w)
	LONG n,w;
	{
	LONG val= w,bno,nset,index;
	for (bno=0l;bno<INT_SZ;bno+=BYTE_SZ,val>>=BYTE_SZ)
	  if((nset=byte_sz[index=val&0xff])<n) n-=nset;
	  else {
	    bno+=bitsinc[index][n-1];
	    break;
	  }
	return(bno);
}

/*
 * b_sample(m,bs) - randomly choose m elements of the bitset
 *	bs and return sampled set.
 */

ITEM
b_sample(m,bs)
	LONG m;
	ITEM bs;
	{
	LONG size;
	ITEM result=B_EMPTY;
	BLOCK b=(BLOCK)I_GET(bs),bsum=b_bitsum(b,&size);
	struct otree *tree=ot_sample(m,size);
	b_sample1(tree,b,bsum,result);
	ot_delete(tree); b_delete(bsum);
	return(result);
}

b_sample1(tree,b,bsum,result)
	struct otree *tree;
	BLOCK b,bsum;
	ITEM result;
	{
	if(tree) {
		b_sample1(tree->left,b,bsum,result);
		b_add(b_findnth(tree->val,b,bsum),result);
		b_sample1(tree->right,b,bsum,result);
	}
}
