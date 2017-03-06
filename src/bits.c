
/* ####################################################################### */

/*                      	Bitsets					   */
/*                      	-------					   */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/*
 * Bitsets allow fast set operations. Sets are stored in blocks of bits
 *	as subsets of a global superset. An element is in the subset if
 *	its corresponding bit is set. Blocks are stored as arrays of
 *	unsigned long ints. The first number in the block indicates
 *	how many long ints are in the array. Set operations can be
 *	carried out by simply &ing and |ing long ints. To avoid
 *	block sizes changing too rapidly as elements are added to
 *	the superset, block sizes are multiples of 128 bits (4 long ints).
 *	This also avoids memory fragmentation.
 */

/*
 * b_spcreate(logh) - creates a bitset superset. Elements are
 *	Array - of elements
 *	Htable - element->number (of size 2^logh)
 *	Max - Max element no in Array + 1
 */

ITEM
b_spcreate(logh)
	LONG logh;
	{
	return(i_tup3(i_dec(i_create('f',(FUNC)f_zero(f_create(64l)))),
		i_dec(h_create(logh)),i_dec(I_INT(0l))));
}

/*
 * b_stob/2 - converts a list into a bitset which corresponds to
 *	the given superset.
 */

unsigned long int *ar_create();

ITEM
b_stob(super,set)
	ITEM super,set;
	{
	ITEM *sarr=((FUNC)I_GET(super))->arr,
		arr= *sarr++,htable= *sarr++,smax= *sarr++,
		*entry,newi;
	register unsigned long int index,nosi=1,*nosp;
	LONG aralloc;
	unsigned long int *nos=ar_create(aralloc=((int)I_GET(smax)<<1));
	register LIST elem;
	BLOCK b,bp1,bp2;
	LIST_LOOP(elem,(LIST)I_GET(set)) {
	    if (!(*(entry=h_ins(newi=L_GET(elem),htable)))) {
		if(nosi>= *nos) ar_enlarge(&nos);
/*
		index = nos[nosi++] = I_NINC1(smax);
		*entry=i_create('i',index);
		*entry=i_create('i',(index= (nos[nosi++] =I_NINC(smax)));
*/
		*entry=i_create('i',(index= (nos[nosi++] =I_NINC1(smax))));
		if (F_SIZE(arr) <= index) f_enlarge(arr);
		F_ELEM(index,arr)=i_inc(newi);
	    }
	    else {
		if(nosi>= *nos) ar_enlarge(&nos);
		nos[nosi++] =(LONG)I_GET(*entry);
	    }
	}
	b=b_create(aralloc=((int)I_GET(smax)>>LOG_INT_SZ));
	nosp=nos+nosi;
	while(--nosp>nos) b[(*nosp>>LOG_INT_SZ)+1] |=
		1 << (*nosp & (INT_SZ - 1));
	ar_delete(nos);
	return(i_create('b',(POINTER)b));
}

/*
 * b_create/1 - constructs a block with the given number of unsigned
 *	long ints. The block is initialised to all zeros. Rounds up
 *	number of integers allocated.
 */
#define	BTOW(n) (((n)+4)& ~3)
		/* Rounds up no of integers to nearest multiple of 4
		   This avoids fragmenting allocation memory
		 */
/* #define	BTOW(n) (1l<<(LOG2(n+1)+1)) */
		/* Rounds up no of integers to nearest power of 2
		   This avoids fragmenting allocation memory
		 */
BLOCK
b_create(size)
	LONG size;
	{
	register BLOCK result,bp,bf;
	char mess[MAXWORD];
	size=BTOW(size);
	if (!(result = (BLOCK)GOLEM_CALLOC(size+1,sizeof(unsigned long int),
			"b_create"))) {
		sprintf(mess,"b_create - calloc failure (size=%d,mem=%d)",
			size,memout);
		d_error(mess);
	}
	B_SIZE(result)=size;
	BLOCK_LOOP(bp,bf,result) *bp=0l;
	return(result);
}

/*
 * b_copy1/2 - copies b2 onto b1. If b1 smaller than b2 then not all
 *	values will be copied.
 */

BLOCK
b_copy1(b1,b2)
	BLOCK b1,b2;
	{
	register BLOCK bp1,bp2,bf1,bf2;
	BLOCK_LOOP2(bp1,bp2,bf1,bf2,b1,b2) *bp1= *bp2;
	return(b1);
}

/*
 * b_copy/1 - make an item with a copy of the given bitset
 */

ITEM
b_copy(bs)
	ITEM bs;
	{
	BLOCK b=(BLOCK)I_GET(bs);
	return(i_create('b',(POINTER)b_copy1(b_create(B_SIZE(b)-1),b)));
}

int
b_delete(b)
	BLOCK b;
	{
	GOLEM_CFREE(b,(B_SIZE(b)+1)*sizeof(unsigned long int),"b_delete");
}

/*
 * bitspos is a table indicating the position of bits that are set
 *	in a byte. The numbers in a row indicate succesive
 *	increments from the last bit that was set. The increments
 *	are terminated by -1 followed by the necessary increment
 *	to skip to the beginning of the next byte.
 */

LONG bitspos[BYTE_RNG] [10] =
{{-1, 8, 0, 0, 0, 0, 0, 0, 0, 0}, {0, -1, 8, 0, 0, 0, 0, 0, 0, 0},
 {1, -1, 7, 0, 0, 0, 0, 0, 0, 0}, {0, 1, -1, 7, 0, 0, 0, 0, 0, 0},
 {2, -1, 6, 0, 0, 0, 0, 0, 0, 0}, {0, 2, -1, 6, 0, 0, 0, 0, 0, 0},
 {1, 1, -1, 6, 0, 0, 0, 0, 0, 0}, {0, 1, 1, -1, 6, 0, 0, 0, 0, 0},
 {3, -1, 5, 0, 0, 0, 0, 0, 0, 0}, {0, 3, -1, 5, 0, 0, 0, 0, 0, 0},
 {1, 2, -1, 5, 0, 0, 0, 0, 0, 0}, {0, 1, 2, -1, 5, 0, 0, 0, 0, 0},
 {2, 1, -1, 5, 0, 0, 0, 0, 0, 0}, {0, 2, 1, -1, 5, 0, 0, 0, 0, 0},
 {1, 1, 1, -1, 5, 0, 0, 0, 0, 0}, {0, 1, 1, 1, -1, 5, 0, 0, 0, 0},
 {4, -1, 4, 0, 0, 0, 0, 0, 0, 0}, {0, 4, -1, 4, 0, 0, 0, 0, 0, 0},
 {1, 3, -1, 4, 0, 0, 0, 0, 0, 0}, {0, 1, 3, -1, 4, 0, 0, 0, 0, 0},
 {2, 2, -1, 4, 0, 0, 0, 0, 0, 0}, {0, 2, 2, -1, 4, 0, 0, 0, 0, 0},
 {1, 1, 2, -1, 4, 0, 0, 0, 0, 0}, {0, 1, 1, 2, -1, 4, 0, 0, 0, 0},
 {3, 1, -1, 4, 0, 0, 0, 0, 0, 0}, {0, 3, 1, -1, 4, 0, 0, 0, 0, 0},
 {1, 2, 1, -1, 4, 0, 0, 0, 0, 0}, {0, 1, 2, 1, -1, 4, 0, 0, 0, 0},
 {2, 1, 1, -1, 4, 0, 0, 0, 0, 0}, {0, 2, 1, 1, -1, 4, 0, 0, 0, 0},
 {1, 1, 1, 1, -1, 4, 0, 0, 0, 0}, {0, 1, 1, 1, 1, -1, 4, 0, 0, 0},
 {5, -1, 3, 0, 0, 0, 0, 0, 0, 0}, {0, 5, -1, 3, 0, 0, 0, 0, 0, 0},
 {1, 4, -1, 3, 0, 0, 0, 0, 0, 0}, {0, 1, 4, -1, 3, 0, 0, 0, 0, 0},
 {2, 3, -1, 3, 0, 0, 0, 0, 0, 0}, {0, 2, 3, -1, 3, 0, 0, 0, 0, 0},
 {1, 1, 3, -1, 3, 0, 0, 0, 0, 0}, {0, 1, 1, 3, -1, 3, 0, 0, 0, 0},
 {3, 2, -1, 3, 0, 0, 0, 0, 0, 0}, {0, 3, 2, -1, 3, 0, 0, 0, 0, 0},
 {1, 2, 2, -1, 3, 0, 0, 0, 0, 0}, {0, 1, 2, 2, -1, 3, 0, 0, 0, 0},
 {2, 1, 2, -1, 3, 0, 0, 0, 0, 0}, {0, 2, 1, 2, -1, 3, 0, 0, 0, 0},
 {1, 1, 1, 2, -1, 3, 0, 0, 0, 0}, {0, 1, 1, 1, 2, -1, 3, 0, 0, 0},
 {4, 1, -1, 3, 0, 0, 0, 0, 0, 0}, {0, 4, 1, -1, 3, 0, 0, 0, 0, 0},
 {1, 3, 1, -1, 3, 0, 0, 0, 0, 0}, {0, 1, 3, 1, -1, 3, 0, 0, 0, 0},
 {2, 2, 1, -1, 3, 0, 0, 0, 0, 0}, {0, 2, 2, 1, -1, 3, 0, 0, 0, 0},
 {1, 1, 2, 1, -1, 3, 0, 0, 0, 0}, {0, 1, 1, 2, 1, -1, 3, 0, 0, 0},
 {3, 1, 1, -1, 3, 0, 0, 0, 0, 0}, {0, 3, 1, 1, -1, 3, 0, 0, 0, 0},
 {1, 2, 1, 1, -1, 3, 0, 0, 0, 0}, {0, 1, 2, 1, 1, -1, 3, 0, 0, 0},
 {2, 1, 1, 1, -1, 3, 0, 0, 0, 0}, {0, 2, 1, 1, 1, -1, 3, 0, 0, 0},
 {1, 1, 1, 1, 1, -1, 3, 0, 0, 0}, {0, 1, 1, 1, 1, 1, -1, 3, 0, 0},
 {6, -1, 2, 0, 0, 0, 0, 0, 0, 0}, {0, 6, -1, 2, 0, 0, 0, 0, 0, 0},
 {1, 5, -1, 2, 0, 0, 0, 0, 0, 0}, {0, 1, 5, -1, 2, 0, 0, 0, 0, 0},
 {2, 4, -1, 2, 0, 0, 0, 0, 0, 0}, {0, 2, 4, -1, 2, 0, 0, 0, 0, 0},
 {1, 1, 4, -1, 2, 0, 0, 0, 0, 0}, {0, 1, 1, 4, -1, 2, 0, 0, 0, 0},
 {3, 3, -1, 2, 0, 0, 0, 0, 0, 0}, {0, 3, 3, -1, 2, 0, 0, 0, 0, 0},
 {1, 2, 3, -1, 2, 0, 0, 0, 0, 0}, {0, 1, 2, 3, -1, 2, 0, 0, 0, 0},
 {2, 1, 3, -1, 2, 0, 0, 0, 0, 0}, {0, 2, 1, 3, -1, 2, 0, 0, 0, 0},
 {1, 1, 1, 3, -1, 2, 0, 0, 0, 0}, {0, 1, 1, 1, 3, -1, 2, 0, 0, 0},
 {4, 2, -1, 2, 0, 0, 0, 0, 0, 0}, {0, 4, 2, -1, 2, 0, 0, 0, 0, 0},
 {1, 3, 2, -1, 2, 0, 0, 0, 0, 0}, {0, 1, 3, 2, -1, 2, 0, 0, 0, 0},
 {2, 2, 2, -1, 2, 0, 0, 0, 0, 0}, {0, 2, 2, 2, -1, 2, 0, 0, 0, 0},
 {1, 1, 2, 2, -1, 2, 0, 0, 0, 0}, {0, 1, 1, 2, 2, -1, 2, 0, 0, 0},
 {3, 1, 2, -1, 2, 0, 0, 0, 0, 0}, {0, 3, 1, 2, -1, 2, 0, 0, 0, 0},
 {1, 2, 1, 2, -1, 2, 0, 0, 0, 0}, {0, 1, 2, 1, 2, -1, 2, 0, 0, 0},
 {2, 1, 1, 2, -1, 2, 0, 0, 0, 0}, {0, 2, 1, 1, 2, -1, 2, 0, 0, 0},
 {1, 1, 1, 1, 2, -1, 2, 0, 0, 0}, {0, 1, 1, 1, 1, 2, -1, 2, 0, 0},
 {5, 1, -1, 2, 0, 0, 0, 0, 0, 0}, {0, 5, 1, -1, 2, 0, 0, 0, 0, 0},
 {1, 4, 1, -1, 2, 0, 0, 0, 0, 0}, {0, 1, 4, 1, -1, 2, 0, 0, 0, 0},
 {2, 3, 1, -1, 2, 0, 0, 0, 0, 0}, {0, 2, 3, 1, -1, 2, 0, 0, 0, 0},
 {1, 1, 3, 1, -1, 2, 0, 0, 0, 0}, {0, 1, 1, 3, 1, -1, 2, 0, 0, 0},
 {3, 2, 1, -1, 2, 0, 0, 0, 0, 0}, {0, 3, 2, 1, -1, 2, 0, 0, 0, 0},
 {1, 2, 2, 1, -1, 2, 0, 0, 0, 0}, {0, 1, 2, 2, 1, -1, 2, 0, 0, 0},
 {2, 1, 2, 1, -1, 2, 0, 0, 0, 0}, {0, 2, 1, 2, 1, -1, 2, 0, 0, 0},
 {1, 1, 1, 2, 1, -1, 2, 0, 0, 0}, {0, 1, 1, 1, 2, 1, -1, 2, 0, 0},
 {4, 1, 1, -1, 2, 0, 0, 0, 0, 0}, {0, 4, 1, 1, -1, 2, 0, 0, 0, 0},
 {1, 3, 1, 1, -1, 2, 0, 0, 0, 0}, {0, 1, 3, 1, 1, -1, 2, 0, 0, 0},
 {2, 2, 1, 1, -1, 2, 0, 0, 0, 0}, {0, 2, 2, 1, 1, -1, 2, 0, 0, 0},
 {1, 1, 2, 1, 1, -1, 2, 0, 0, 0}, {0, 1, 1, 2, 1, 1, -1, 2, 0, 0},
 {3, 1, 1, 1, -1, 2, 0, 0, 0, 0}, {0, 3, 1, 1, 1, -1, 2, 0, 0, 0},
 {1, 2, 1, 1, 1, -1, 2, 0, 0, 0}, {0, 1, 2, 1, 1, 1, -1, 2, 0, 0},
 {2, 1, 1, 1, 1, -1, 2, 0, 0, 0}, {0, 2, 1, 1, 1, 1, -1, 2, 0, 0},
 {1, 1, 1, 1, 1, 1, -1, 2, 0, 0}, {0, 1, 1, 1, 1, 1, 1, -1, 2, 0},
 {7, -1, 1, 0, 0, 0, 0, 0, 0, 0}, {0, 7, -1, 1, 0, 0, 0, 0, 0, 0},
 {1, 6, -1, 1, 0, 0, 0, 0, 0, 0}, {0, 1, 6, -1, 1, 0, 0, 0, 0, 0},
 {2, 5, -1, 1, 0, 0, 0, 0, 0, 0}, {0, 2, 5, -1, 1, 0, 0, 0, 0, 0},
 {1, 1, 5, -1, 1, 0, 0, 0, 0, 0}, {0, 1, 1, 5, -1, 1, 0, 0, 0, 0},
 {3, 4, -1, 1, 0, 0, 0, 0, 0, 0}, {0, 3, 4, -1, 1, 0, 0, 0, 0, 0},
 {1, 2, 4, -1, 1, 0, 0, 0, 0, 0}, {0, 1, 2, 4, -1, 1, 0, 0, 0, 0},
 {2, 1, 4, -1, 1, 0, 0, 0, 0, 0}, {0, 2, 1, 4, -1, 1, 0, 0, 0, 0},
 {1, 1, 1, 4, -1, 1, 0, 0, 0, 0}, {0, 1, 1, 1, 4, -1, 1, 0, 0, 0},
 {4, 3, -1, 1, 0, 0, 0, 0, 0, 0}, {0, 4, 3, -1, 1, 0, 0, 0, 0, 0},
 {1, 3, 3, -1, 1, 0, 0, 0, 0, 0}, {0, 1, 3, 3, -1, 1, 0, 0, 0, 0},
 {2, 2, 3, -1, 1, 0, 0, 0, 0, 0}, {0, 2, 2, 3, -1, 1, 0, 0, 0, 0},
 {1, 1, 2, 3, -1, 1, 0, 0, 0, 0}, {0, 1, 1, 2, 3, -1, 1, 0, 0, 0},
 {3, 1, 3, -1, 1, 0, 0, 0, 0, 0}, {0, 3, 1, 3, -1, 1, 0, 0, 0, 0},
 {1, 2, 1, 3, -1, 1, 0, 0, 0, 0}, {0, 1, 2, 1, 3, -1, 1, 0, 0, 0},
 {2, 1, 1, 3, -1, 1, 0, 0, 0, 0}, {0, 2, 1, 1, 3, -1, 1, 0, 0, 0},
 {1, 1, 1, 1, 3, -1, 1, 0, 0, 0}, {0, 1, 1, 1, 1, 3, -1, 1, 0, 0},
 {5, 2, -1, 1, 0, 0, 0, 0, 0, 0}, {0, 5, 2, -1, 1, 0, 0, 0, 0, 0},
 {1, 4, 2, -1, 1, 0, 0, 0, 0, 0}, {0, 1, 4, 2, -1, 1, 0, 0, 0, 0},
 {2, 3, 2, -1, 1, 0, 0, 0, 0, 0}, {0, 2, 3, 2, -1, 1, 0, 0, 0, 0},
 {1, 1, 3, 2, -1, 1, 0, 0, 0, 0}, {0, 1, 1, 3, 2, -1, 1, 0, 0, 0},
 {3, 2, 2, -1, 1, 0, 0, 0, 0, 0}, {0, 3, 2, 2, -1, 1, 0, 0, 0, 0},
 {1, 2, 2, 2, -1, 1, 0, 0, 0, 0}, {0, 1, 2, 2, 2, -1, 1, 0, 0, 0},
 {2, 1, 2, 2, -1, 1, 0, 0, 0, 0}, {0, 2, 1, 2, 2, -1, 1, 0, 0, 0},
 {1, 1, 1, 2, 2, -1, 1, 0, 0, 0}, {0, 1, 1, 1, 2, 2, -1, 1, 0, 0},
 {4, 1, 2, -1, 1, 0, 0, 0, 0, 0}, {0, 4, 1, 2, -1, 1, 0, 0, 0, 0},
 {1, 3, 1, 2, -1, 1, 0, 0, 0, 0}, {0, 1, 3, 1, 2, -1, 1, 0, 0, 0},
 {2, 2, 1, 2, -1, 1, 0, 0, 0, 0}, {0, 2, 2, 1, 2, -1, 1, 0, 0, 0},
 {1, 1, 2, 1, 2, -1, 1, 0, 0, 0}, {0, 1, 1, 2, 1, 2, -1, 1, 0, 0},
 {3, 1, 1, 2, -1, 1, 0, 0, 0, 0}, {0, 3, 1, 1, 2, -1, 1, 0, 0, 0},
 {1, 2, 1, 1, 2, -1, 1, 0, 0, 0}, {0, 1, 2, 1, 1, 2, -1, 1, 0, 0},
 {2, 1, 1, 1, 2, -1, 1, 0, 0, 0}, {0, 2, 1, 1, 1, 2, -1, 1, 0, 0},
 {1, 1, 1, 1, 1, 2, -1, 1, 0, 0}, {0, 1, 1, 1, 1, 1, 2, -1, 1, 0},
 {6, 1, -1, 1, 0, 0, 0, 0, 0, 0}, {0, 6, 1, -1, 1, 0, 0, 0, 0, 0},
 {1, 5, 1, -1, 1, 0, 0, 0, 0, 0}, {0, 1, 5, 1, -1, 1, 0, 0, 0, 0},
 {2, 4, 1, -1, 1, 0, 0, 0, 0, 0}, {0, 2, 4, 1, -1, 1, 0, 0, 0, 0},
 {1, 1, 4, 1, -1, 1, 0, 0, 0, 0}, {0, 1, 1, 4, 1, -1, 1, 0, 0, 0},
 {3, 3, 1, -1, 1, 0, 0, 0, 0, 0}, {0, 3, 3, 1, -1, 1, 0, 0, 0, 0},
 {1, 2, 3, 1, -1, 1, 0, 0, 0, 0}, {0, 1, 2, 3, 1, -1, 1, 0, 0, 0},
 {2, 1, 3, 1, -1, 1, 0, 0, 0, 0}, {0, 2, 1, 3, 1, -1, 1, 0, 0, 0},
 {1, 1, 1, 3, 1, -1, 1, 0, 0, 0}, {0, 1, 1, 1, 3, 1, -1, 1, 0, 0},
 {4, 2, 1, -1, 1, 0, 0, 0, 0, 0}, {0, 4, 2, 1, -1, 1, 0, 0, 0, 0},
 {1, 3, 2, 1, -1, 1, 0, 0, 0, 0}, {0, 1, 3, 2, 1, -1, 1, 0, 0, 0},
 {2, 2, 2, 1, -1, 1, 0, 0, 0, 0}, {0, 2, 2, 2, 1, -1, 1, 0, 0, 0},
 {1, 1, 2, 2, 1, -1, 1, 0, 0, 0}, {0, 1, 1, 2, 2, 1, -1, 1, 0, 0},
 {3, 1, 2, 1, -1, 1, 0, 0, 0, 0}, {0, 3, 1, 2, 1, -1, 1, 0, 0, 0},
 {1, 2, 1, 2, 1, -1, 1, 0, 0, 0}, {0, 1, 2, 1, 2, 1, -1, 1, 0, 0},
 {2, 1, 1, 2, 1, -1, 1, 0, 0, 0}, {0, 2, 1, 1, 2, 1, -1, 1, 0, 0},
 {1, 1, 1, 1, 2, 1, -1, 1, 0, 0}, {0, 1, 1, 1, 1, 2, 1, -1, 1, 0},
 {5, 1, 1, -1, 1, 0, 0, 0, 0, 0}, {0, 5, 1, 1, -1, 1, 0, 0, 0, 0},
 {1, 4, 1, 1, -1, 1, 0, 0, 0, 0}, {0, 1, 4, 1, 1, -1, 1, 0, 0, 0},
 {2, 3, 1, 1, -1, 1, 0, 0, 0, 0}, {0, 2, 3, 1, 1, -1, 1, 0, 0, 0},
 {1, 1, 3, 1, 1, -1, 1, 0, 0, 0}, {0, 1, 1, 3, 1, 1, -1, 1, 0, 0},
 {3, 2, 1, 1, -1, 1, 0, 0, 0, 0}, {0, 3, 2, 1, 1, -1, 1, 0, 0, 0},
 {1, 2, 2, 1, 1, -1, 1, 0, 0, 0}, {0, 1, 2, 2, 1, 1, -1, 1, 0, 0},
 {2, 1, 2, 1, 1, -1, 1, 0, 0, 0}, {0, 2, 1, 2, 1, 1, -1, 1, 0, 0},
 {1, 1, 1, 2, 1, 1, -1, 1, 0, 0}, {0, 1, 1, 1, 2, 1, 1, -1, 1, 0},
 {4, 1, 1, 1, -1, 1, 0, 0, 0, 0}, {0, 4, 1, 1, 1, -1, 1, 0, 0, 0},
 {1, 3, 1, 1, 1, -1, 1, 0, 0, 0}, {0, 1, 3, 1, 1, 1, -1, 1, 0, 0},
 {2, 2, 1, 1, 1, -1, 1, 0, 0, 0}, {0, 2, 2, 1, 1, 1, -1, 1, 0, 0},
 {1, 1, 2, 1, 1, 1, -1, 1, 0, 0}, {0, 1, 1, 2, 1, 1, 1, -1, 1, 0},
 {3, 1, 1, 1, 1, -1, 1, 0, 0, 0}, {0, 3, 1, 1, 1, 1, -1, 1, 0, 0},
 {1, 2, 1, 1, 1, 1, -1, 1, 0, 0}, {0, 1, 2, 1, 1, 1, 1, -1, 1, 0},
 {2, 1, 1, 1, 1, 1, -1, 1, 0, 0}, {0, 2, 1, 1, 1, 1, 1, -1, 1, 0},
 {1, 1, 1, 1, 1, 1, 1, -1, 1, 0}, {0, 1, 1, 1, 1, 1, 1, 1, -1, 1}};


/*
 * b_btos/2 - constructs a list from a bitset and its corresponding
 *	superset. b_btos uses bitspos to rapidly decode bytes.
 */

ITEM
b_btos(super,bits)
	ITEM super,bits; {
	ITEM result;
	register ITEM *sarr=((FUNC)I_GET(
		*(((FUNC)I_GET(super))->arr)))->arr;
	register LIST *last=L_LAST(result=L_EMPTY);
	BIT_DO(sarr,bits)
	  last=l_end(i_inc(*sarr),last);
	BIT_END
	return(result);
}

/*
 * b_first/1 - returns the number corresponding to the first element
 *	in the bitset
 */

LONG
b_first(bits)
	ITEM bits;
	{
	register result=0l;
	BIT_DO(result,bits)
	    return(result);
	BIT_END
	d_error("b_first - handed empty bitset");
}

/*
 * b_ith/2 - returns the ith mod cardinality from bitset
 */

LONG
b_ith(i,bits)
	register LONG i;
	ITEM bits;
	{
	register LONG result=0l,size;
	if(size=b_size(bits)) i=((i-1)%b_size(bits))+1;
	else d_error("b_ith - handed empty bitset");
	BIT_DO(result,bits)
	    if(--i == 0l) return(result);
	BIT_END
}

/*
 * b_elem - returns the element in the superset corresponding to the
 *	given number.
 */

ITEM
b_elem(n,super)
	LONG n;
	ITEM super;
	{
	return(i_inc(F_ELEM(n,F_ELEM(0l,super))));
}

/*
 * b_int/2 - destructively intersects 2 bitsets by iteratively
 *	&ing. The result overwrites the first argument.
 */

ITEM
b_int(bs1,bs2)
	ITEM bs1,bs2;
	{
	register BLOCK bp1,bp2,bf1,bf2,b1=(BLOCK)I_GET(bs1),
		b2=(BLOCK)I_GET(bs2);
	BLOCK_LOOP2(bp1,bp2,bf1,bf2,b1,b2) *bp1 &= *bp2;
	while(bp1 <= bf1) *bp1++ = 0;
	return(bs1);
}

/*
 * b_sub/2 - destructively subtracts 2 bitsets by iteratively
 *	&ing and ~ing. The result overwrites the first argument.
 */

ITEM
b_sub(bs1,bs2)
	ITEM bs1,bs2;
	{
	register BLOCK bp1,bp2,bf1,bf2,b1=(BLOCK)I_GET(bs1),
		b2=(BLOCK)I_GET(bs2);
	/* BLOCK_LOOP2(bp1,bp2,bf1,bf2,b1,b2) *bp1 ^= *bp1 & *bp2; */
	BLOCK_LOOP2(bp1,bp2,bf1,bf2,b1,b2) *bp1 &= ~(*bp2);
	return(bs1);
}

/*
 * b_uni/2 - destructively takes union of 2 bitsets by iteratively
 *	|ing. The result overwrites the first argument.
 */

ITEM
b_uni(bs1,bs2)
	ITEM bs1,bs2;
	{
	register BLOCK bp1,bp2,bf1,bf2,b1=(BLOCK)I_GET(bs1),
		b2=(BLOCK)I_GET(bs2),newb;
	if (B_SIZE(b1) < B_SIZE(b2)) {
		newb=b_copy1(b_create(B_SIZE(b2)-1),b1);
		b_delete(b1);
		(BLOCK)I_GET(bs1)=(b1=newb);
	}
	BLOCK_LOOP2(bp1,bp2,bf1,bf2,b1,b2) *bp1 |= *bp2;
	return(bs1);
}

/*
 * b_subseteq/2 - decides whether the first set is a subset
 *	of the second
 */

PREDICATE
b_subseteq(bs1,bs2)
	ITEM bs1,bs2;
	{
	register BLOCK bp1,bp2,bf1,bf2,b1=(BLOCK)I_GET(bs1),
		b2=(BLOCK)I_GET(bs2);
	BLOCK_LOOP2(bp1,bp2,bf1,bf2,b1,b2)
		if(*bp1 & ~(*bp2)) return(FALSE);
	return(TRUE);
}

/*
 * b_size/1 - calculates the cardinality of a bitset. This is done
 *      quickly by using the global array byte_sz for counting the number
 *      of bits set eight at a time.
 */


unsigned char byte_sz[BYTE_RNG] =
	{0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,
	 1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
	 1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
	 2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
	 1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,
	 2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
	 2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,
	 3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7,4,5,5,6,5,6,6,7,5,6,6,7,6,7,7,8};

unsigned char log2[BYTE_RNG] =
	{255,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,4,
	 5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,
	 6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,
	 6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,
	 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
	 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
	 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,
	 7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7,7};

LONG
b_size(bs)
	ITEM bs;
	{
	register LONG result=0,cnt;
	register unsigned long int val;
	register BLOCK bp,be,b=(BLOCK)I_GET(bs);
	BLOCK_LOOP(bp,be,b) {
	  if (!(val= *bp)) continue;
	  for (cnt=0l;cnt<INT_SZ;cnt+=BYTE_SZ,val>>=BYTE_SZ)
	    result+= byte_sz[val&0xff];
	}
	return(result);
}

/*
 * b_trunc/2 - destructively truncates the bitset by zeroing
 *	all but the first limit bits.
 */

int
b_trunc(bs,limit)
	ITEM bs;
	register limit;
	{
	register LONG sofar=0,cnt;
	register unsigned long int val;
	register BLOCK bp,be,b=(BLOCK)I_GET(bs);
	register PREDICATE trunc=FALSE;
	BLOCK_LOOP(bp,be,b) {
	  if (trunc) *bp=0l;
	  else {
	    if (!(val= *bp)) continue;
	    for (cnt=0l;cnt<INT_SZ;cnt+=BYTE_SZ,val>>=BYTE_SZ)
	      if ((sofar += byte_sz[val&0xff])>limit)
		trunc=TRUE;
	    if (trunc) {
	      for(cnt=1;cnt<=INT_SZ;cnt++) {
		if ((*bp & 1<<31)&& --sofar==limit) {
		  *bp<<=1;
		  break;
		}
		else *bp<<=1;
	      }
	      *bp>>=cnt;
	    }
	  }
	}
}

PREDICATE
b_emptyq(bs)
	ITEM bs;
	{
	register BLOCK bp,be,b=(BLOCK)I_GET(bs);
	BLOCK_LOOP(bp,be,b) if (*bp) return(FALSE);
	return(TRUE);
}

/* b_add/2 - destructively sets the given bit number in the bitset.
 */

ITEM
b_add(n,bs)
	LONG n;
	ITEM bs;
	{
	register BLOCK b,newb;
	register LONG index;
	if (B_SIZE(b=(BLOCK)I_GET(bs)) < (index=(n>>LOG_INT_SZ)+1l)) {
		newb=b_copy1(b_create(index),b);
		b_delete(b);
		(BLOCK)I_GET(bs)=(b=newb);
	}
	b[index] |= 1 << (n & (INT_SZ - 1));
	return(bs);
}

/* b_rem/2 - destructively unsets the given bit number in the bitset.
 */

ITEM
b_rem(n,bs)
	LONG n;
	ITEM bs;
	{
	register BLOCK b;
	register LONG index;
	if (B_SIZE(b=(BLOCK)I_GET(bs)) >= (index=(n>>LOG_INT_SZ)+1))
		b[index] &= ~(1 << (n & (INT_SZ - 1)));
	return(bs);
}

/*
 * b_num/2 - returns the number associated with the given element
 *	in the given superset.
 */

LONG
b_num(e,super)
	ITEM e,super;
	{
	ITEM *sarr=((FUNC)I_GET(super))->arr,
		arr= *sarr++,htable= *sarr++,smax= *sarr++,
		*entry;
	LONG result;
	if (!(*(entry=h_ins(e,htable)))) {
/*
	    *entry=i_create('i',result= I_NINC(smax));
*/
	    *entry=i_create('i',result= I_NINC1(smax));
	    if (F_SIZE(arr) <= result)
		f_enlarge(arr);
	    F_ELEM(result,arr)=i_inc(e);
	}
	else result =(LONG)I_GET(*entry);
	return(result);
}

/*
 * b_memq - given number and bitset, checks whether the
 *	given bit is set.
 */

PREDICATE
b_memq(n,bs)
	LONG n;
	ITEM bs;
	{
	register BLOCK b;
	register LONG index;
	if (B_SIZE(b=(BLOCK)I_GET(bs)) >= (index=(n>>LOG_INT_SZ)+1))
	    if (b[index] & (1 << (n & (INT_SZ - 1)))) return(TRUE);
	return(FALSE);
}

/*
 * b_allones(size) - create a bitset containing bits set up
 *	to size.
 */

#define	ALLONES	0xFFFFFFFF

ITEM 
b_allones(size)
	register LONG size;
	{
	ITEM result=i_create('b',(POINTER)b_create((size-1)>>(LOG_INT_SZ)));
	BLOCK b=(BLOCK)I_GET(result);
	register BLOCK bp,bend;
	BLOCK_LOOP(bp,bend,b)
	    if (size <= INT_SZ) {*bp=ALLONES;*bp>>=(INT_SZ-size);break;}
	    else {*bp=ALLONES;size-=INT_SZ;}
	return(result);
}

/*
 * ar_create/1 - create an array of integers.
 */

unsigned long int *
ar_create(size)
	unsigned long int size;
	{
	unsigned long int *result,*arp,*arend;
	size=(size>0?size:1);
	if (!(result = (unsigned long int *)GOLEM_CALLOC(size+1,
		  sizeof(unsigned long int),"ar_create")))
		d_error("ar_create - calloc failure");
	*result=size;
	AR_LOOP(arp,arend,result) *arp=0l;
	return(result);
}

int
ar_delete(arr)
	unsigned long int *arr;
	{
	GOLEM_CFREE(arr,(*arr+1)*
		sizeof(unsigned long int),"ar_delete");
}

/*
 * ar_enlarge/1 - double the size of an array of integers, copying
 *	old to new.
 */

int
ar_enlarge(nospp)
	unsigned long int **nospp;
	{
	unsigned long int *oldar= *nospp,oldsize= *oldar,
		*result=ar_create(((oldsize+2l)<<1l)-2l),
		*p1= oldar+oldsize,*p2=result+oldsize;
	while(p1 > oldar) *p2-- = *p1--;
	ar_delete(oldar);
	*nospp=result;
}

/*
 * ar_push - integer arrays can be used as a stack by using
 *	the second integer array value as a stack pointer.
 *	Integer arrays can be used as items of type 'y'.
 *	ar_push enlarges the stack if necessary.
 */

int
ar_push(v,ar)
	unsigned long int v;
	unsigned long int **ar;
	{
	unsigned long int *stackp;
	if ((*(stackp=(*ar+1))+1) >= **ar) {
		ar_enlarge(ar);
		stackp= *ar + 1;
	}
	*(*ar + (*stackp)++ + 2) = v;
}

/*
 * ar_pop - pops and returns the top integer, decrements the
 *	stack pointer and replaces value by zero in the array.
 *	Returns I_TERM if stack is empty
 */

unsigned long int
ar_pop(ar)
	unsigned long int *ar;
	{
	unsigned long int result,*stackp,*top;
	if(!(*(stackp=ar+1))) return((unsigned long int)I_TERM);
	result= *(top=(ar + (*stackp)-- + 1l));
	*top= 0l;
	return(result);
}

/* y_ins(n,y) - insertion for integer array. Returns
 *	pointer to position in integer array. The array is
 *	expanded if necessary.
 */

BLOCK
y_ins(n,y)
	register LONG n;
	register ITEM y;
	{
	BLOCK *ar=(BLOCK *)(&I_GET(y)),stackp;
	if (n+1l >= **ar) y_enlarge(ar,n);
	if (n >= *(stackp=(*ar+1l))) *stackp=n+1l;
	return(*ar+n+2l);
}

/* y_enlarge(ar,n) - enlarge ar to be the size of the smallest
 *	power of 2 greater than n
 */

int
y_enlarge(ar,n)
	unsigned long int **ar;
	LONG n;
	{
	unsigned long int *oldar= *ar,oldsize= *oldar,
		*result=ar_create((1l<<(LOG2(n+3l)+1l))-2l),
		*p1= oldar+oldsize,*p2=result+oldsize;
	while(p1 > oldar) *p2-- = *p1--;
	ar_delete(oldar);
	*ar=result;
}

/*
 * y_copy/1 - make an item with a copy of the given bitset
 */

ITEM
y_copy(bs)
	ITEM bs;
	{
	BLOCK b=(BLOCK)I_GET(bs);
	return(i_create('y',(POINTER)b_copy1(b_create(B_SIZE(b)-1),b)));
}

/*
 * b_numv/3 - this is the same as b_num but uses a pre-computed
 *	hash number for efficiency
 */

LONG
b_numv(e,he,super)
	ITEM e,super;
	LONG he;
	{
	ITEM *sarr=((FUNC)I_GET(super))->arr,
		arr= *sarr++,htable= *sarr++,smax= *sarr++,
		*entry;
	LONG result;
	register LIST *last;
	FUNC f;
	if (!(*(entry= &(F_ELEM(he&(F_SIZE(htable)-1),htable)))))
		last=L_LAST(*entry=L_EMPTY);
	else for (last= (LIST *)&I_GET(*entry);*last;last= &((*last)->next))
		if (ITMEQ(e,F_ELEM(0l,L_GET(*last)))) break;
	if (*last) /* Already in */
		result= (LONG)I_GET(F_ELEM(1l,L_GET(*last)));
	else {		/* New one */
		l_end(i_create('f',f=f_create(2l)),last);
		*(f->arr) = i_inc(e);
/*
		f->arr[1]= i_create('i',result= I_NINC(smax));
*/
		f->arr[1]= i_create('i',result= I_NINC1(smax));
		if (F_SIZE(arr) <= result)
			f_enlarge(arr);
		F_ELEM(result,arr)=i_inc(e);
	}
	return(result);
}
