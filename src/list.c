#include <stdio.h>
#include "golem.h"

/*
 * #######################################################################
 *
 *                      List Processing Routines
 *                      ------------------------
 *
 * #######################################################################
 */

/* ####################################################################### 
 *
 * Add element to end of list. No search
 *	to the end of list necessary.
 */

LIST *
l_end(val, last)
        register ITEM val;
        register LIST *last;
        {
	register LIST new_mem;
	if (!(new_mem = (LIST)GOLEM_CALLOC(1l, sizeof(struct lmem), "l_end"))) {
                d_error("l_end - GOLEM_CALLOC failed");
        }
	new_mem->pres=val;
	new_mem->next=(LIST)NULL;
	*last=new_mem;
	return(&(new_mem->next));
}

/* ####################################################################### 
 *
 * l_push/2 - push object onto list-based stack. actually just the
 *	same as l_prefix. Usage counter of object unchanged.
 */

ITEM
l_push(val, i)
        ITEM val; 
        ITEM i;
        {
	LIST list;        
	LIST new_mem;

	if (i->item_type != 'l')
		d_error("l_push - item not a list");
	else if (!(new_mem = (LIST)GOLEM_CALLOC(1l,
			sizeof(struct lmem), "l_push")))
                d_error("l-suffix - GOLEM_CALLOC failed");
	else {
		new_mem->pres=i_inc(val);
		list=(LIST)I_GET(i);
		new_mem->next=list;
		(LIST)i->obj=new_mem;
	}
	return(i);
}

/* ####################################################################### 
 *
 * l_pop/ - pops the first object off a list-based stack. Usage counter of
 *		object unchanged.
 */

ITEM
l_pop(l)
	ITEM l;
	{
	LIST list=(LIST)I_GET(l);
	ITEM result;

	if (l->item_type != 'l')
		d_error("l_pop - not handed a list");
	if (!list) d_error("l_pop - handed empty list");
	else {
		result=HOF(list);
		(LIST)I_GET(l)=TOF(list);
		GOLEM_CFREE(list,sizeof(struct lmem),"l_pop");
	}
	return(result);
}

/* ####################################################################### 
 *
 * l_append/2 - destructively appends 2 lists to each other. The first list
 *	is overwritten and returned.
 */

ITEM
l_append(l1,l2)
	ITEM l1,l2;
        {
	register LIST e,*ep;

	if (!l1 || !l2) d_error("l_append - handed NULL pointer");
	else if (l1->item_type != 'l' || l2->item_type != 'l')
		d_error("l_append - not handed lists");
	else {
		LISTP_LOOP(ep,l1);
		LIST_LOOP(e,(LIST)I_GET(l2))
			L_TERM(e,ep);
	}
	return(l1);
}

/*
 * l_length(list) - returns the length of the list
 */

LONG
l_length(list)
	ITEM list;
	{
	register LIST elem;
	register LONG result=0l;
	LIST_LOOP(elem,(LIST)I_GET(list)) result++;
	return(result);
}

/* ####################################################################### 
 *
 * l_reverse/1 - destructive list reverse
 */

ITEM
l_reverse(list)
	ITEM list;
	{
	register LIST rev=(LIST)NULL,firstl=(LIST)I_GET(list),firstr;
	while(firstr=firstl) {
	  firstl= TOF(firstl);	/* Pop list */
	  TOF(firstr)=rev;	/* Push onto rev */
	  rev=firstr;
	}
	(LIST)I_GET(list)=rev;
	return(list);
}

/*
 * l_copy - makes a surface copy of a list. The underlying
 *	structure is not copied.
 */

ITEM
l_copy(l)
	ITEM l;
	{
	ITEM result;
	register LIST elem,*last=L_LAST(result=L_EMPTY);
	LIST_LOOP(elem,(LIST)I_GET(l)) last=l_end(i_inc(L_GET(elem)),last);
	return(result);
}

/*
 * l_rem/1 - removes the given list element.
 */

int
l_rem(elemp)
	LIST *elemp;
	{
	register LIST elem= *elemp;
	*elemp = elem->next;
	i_delete(L_GET(elem));
	GOLEM_CFREE((POINTER)elem,
		sizeof(struct lmem),"l_rem");
}

/*
 * l_ins/2 - the dual of l_rem. Inserts a new item into a list
 *	before the given element. Returns LIST pointer to the
 *	element given as input. If elemp points to NULL, the
 *	effect is the same as l_end, except that the item
 *	pointer is incremented.
 */

LIST *
l_ins(i,elemp)
	ITEM i;
	LIST *elemp;
	{
	register LIST elem= *elemp;
	elemp=l_end(i_inc(i),elemp);
	*elemp=elem;
	return(elemp);
}
