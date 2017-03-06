/* ####################################################################### */

/*                      GOLEM Path-term Routines                           */
/*                      ------------------------                           */

/* ####################################################################### */

#include        <stdio.h>
#include        "golem.h"

/*
 * pt_ins/2 - hashing path/term to a unique number needs to be very fast.
 *	Thus a special hash structure is used. This is an array of
 *	integer arrays. The integer arrays represent lists of records.
 *	The records are arranged as 2 integer cells. The first integer
 *	is the key, a 32 bit number, the lower 16 bits being the term
 *	number, the upper 16 the path number. The second number in the
 *	cell is the actual path-term number. The cell lists are terminated
 *	by a -1. The returned value either points to -1 (missing) or
 *	points to 1 before the number.
 */

#define	PTINIT	16l
LONG *pt_acreate();
LONG *pt_enlarge();

LONG *
pt_ins(p,t)
	LONG p,t;
	{
	register LONG *ip,**ipp,pt=PT(p,t);
	if (!(ip= *(ipp=hpt+HPT(p,t))))
		ip=(*ipp=pt_acreate(PTINIT));
	for(ip++;*ip!= pt && *ip!= PTTERM;ip+=2);
	if((ip- *ipp) == (**ipp)-1) ip=pt_enlarge(ipp);
	return(ip);
}

/*
 * pt_acreate/0 - create and initialise a new list of hash cells
 */

LONG *
pt_acreate(size)
	LONG size;
	{
	LONG *result;
	if (!(result = (LONG *)GOLEM_CALLOC(size, sizeof(LONG), "pt_acreate")))
		d_error("pt_acreate");
	*result=size;
	*(result+1l)= PTTERM;
	return(result);
}

int
pt_adelete(arr)
	LONG *arr;
	{
	GOLEM_CFREE(arr,*arr * sizeof(LONG *),"pt_adelete");
}

/*
 * pt_enlarge/1 - doubles the length of a list of hash cells terminated by
 *	a PTTERM. Return pointer to the terminator.
 */

LONG *
pt_enlarge(ipp)
	LONG **ipp;
	{
	LONG *newlist=pt_acreate((**ipp)<<1),*ip1,*ip2;
	for(ip1= newlist+1,ip2= *ipp+1;*ip2 != PTTERM;*ip1++ = *ip2++);
	*ip1= PTTERM;
	GOLEM_CFREE(*ipp,**ipp * sizeof(LONG *),"pt_enlarge");
	*ipp= newlist;
	*ip1 = PTTERM;
	return(ip1);
}

int
pt_write()
	{
	LONG **ipp,*ip,cnt=0l;
	for(ipp=hpt;ipp < hpt+HASH10+1;ipp++,cnt++) {
	  if (ip = *ipp) {
	    printf("%ld(%ld): ",cnt,*ip++);
	    while(*ip != PTTERM) {
		printf("%ld/%ld->%ld ",PNO(*ip),TNO(*ip),*(ip+1));
		ip+=2;
	    }
	    printf(";\n");
	  }
	}
}
