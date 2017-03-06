/* ####################################################################### */

/*              GOLEM Include File for Structures and #defines             */
/*              --------------------------------------------               */

/* ####################################################################### */

typedef long int LONG;
typedef char *STRING;
typedef char *POINTER;
typedef struct item *ITEM;
typedef struct lmem *LIST;
typedef unsigned long int *BLOCK;
typedef struct functor *FUNC;
typedef struct filerec FILEREC;

/*
#define		MEMCHECK
#define		CHECK_SECURITY
 */
#define		SUNCHECK


extern long rand();
extern void srand();

#define		RAND		rand()
#define		SRAND(x)	srand(x)
#define		MYRAND(lo,hi) ((RAND%(((hi)-(lo))+1))+(lo))

#define		GOLEM_CALLOC(a,b,c)	a_dalloc(a,b)
#define		GOLEM_CFREE(a,b,c)	a_dfree(a,b)

#define         PREDICATE       long int
#define         TRUE            1
#define         FALSE           0
#define		GT		1
#define		EQ		0
#define		LT		-1
#define         MAXMESS         1000l
#define         MAXWORD         200l
#define		BUFSIZE		512l
#define		LBUF		4l
#define		PTTERM		-1
#define		I_TERM		-1l
#define		I_ERROR		-2l
#define		HGEN		0l
#define		HASH10		2047l
#define		INF		9999l
#define		SEP		0l
#define		ALPHN		1l
#define		SYM		2l
#define		OPTR		2l
#define		OPND		3l
#define		ABS		1l
#define		INTRA		2l
#define		IN		-1
#define		OUT		1
#define		UNASS		0xffffffffl
#define		NGRND		0xffffl

#define		PADDING(c)	(c == ' ' || c == '\n' || c == '\t')
#define		DIGIT(c)	(c >= '0' && c <= '9')
#define		LOWCASE(c)	((c) >= 'a' && (c) <= 'z')
#define		UPCASE(c)	((c) >= 'A' && (c) <= 'Z')
#define		ALPHA(c)	(LOWCASE(c) || UPCASE(c))
#define		ALPHANUM(c)	(ALPHA(c) || DIGIT(c) || \
					(c == '_'))
#define		HEX(c)		(DIGIT(c) || (c >= 'A' && c <= 'Z'))
#define		LOG2(n)		((n)&0xffff0000l?((n)&0xff000000l?log2[(n)>>24l]+24l:log2[(n)>>16l]+16l):((n)&0xff00l?log2[(n)>>8l]+8l:log2[n]))
#define		B_SIZE(b)	(*(b))
#define		F_ELEM(n,i)	(((FUNC)I_GET(i))->arr[n])
#define		F_SIZE(i)	(((FUNC)I_GET(i))->arr_size)
#define		FNAME(f)	((f)->arr[0])
#define		S_DEL(s,m)	GOLEM_CFREE((s),strlen(s)+1,(m))
#define		L_DEL(l,m)	GOLEM_CFREE((POINTER)(l),sizeof(struct lmem),(m))
#define         STREQ(s1,s2)    (!strcmp(s1,s2))
#define		STR_LOOP(sp,s)	for((sp) = (s) ; *(sp) ; (sp)++)
#define		NUM_LOOP(n,s,i,f)	for((n) = (s); (n) != ((f) + (i)); (n) += (i))
#define		TERM_LOOP(e,n,p)	for((e)=(p),(n)=1;(n)>0;(n)+=((*(e)>0)?*(e)-1:-1),(e)+=((*(e)>= -2)?2:1))
#define		TERM_LOOP2(e1,n1,e2,n2,p1,p2)	for(e1=(p1),e2=(p2),n1=1,n2=1;(n1)>0 && (n2)>0;(n1)+=((*(e1)>0)? *(e1)-1:-1),(n2)+=((*(e2)>0)? *(e2)-1:-1),(e1)+=((*(e1)>= -2)?2:1),(e2)+=((*(e2)>= -2)?2:1))
#define		ARG_LOOP(ip,f)	for(ip=((f)->arr)+1;ip<(f)->arr+(f)->arr_size;ip++)
#define		ARG_LOOP2(e1,e2,f1,f2)	for(e1=((f1)->arr)+1,e2=((f2)->arr)+1;(e1<((f1)->arr + (f1)->arr_size)) && (e2 < ((f2)->arr + (f2)->arr_size));e1++,e2++)
#define		ARG_LOOP3(e1,e2,e3,f1,f2,f3)	for(e1=((f1)->arr)+1,e2=((f2)->arr)+1,e3=((f3)->arr)+1;(e1<((f1)->arr+(f1)->arr_size))&&(e2<((f2)->arr+(f2)->arr_size))&&(e3<((f3)->arr+(f3)->arr_size));e1++,e2++,e3++)
#define		Y_DO(e,y) {register unsigned long int zf; for((e)=((unsigned long int *)I_GET(y))+1l,zf= *((e)++);zf--;(e)++){
#define		Y_END }}
#define		BLOCK_LOOP(e,f,b) for((e)=(b)+1,(f)=(b)+B_SIZE(b);(e) <= (f);(e)++)
#define		BLOCK_LOOP2(e1,e2,f1,f2,b1,b2) for((e1)=(b1)+1,(e2)=(b2)+1,(f1)=(b1)+B_SIZE(b1),(f2)=(b2)+B_SIZE(b2);(e1)<=(f1)&&(e2)<=(f2);(e1)++,(e2)++)
#define		BIT_LOOP(n,e,f,b,v,c,p) BLOCK_LOOP(e,f,b)if(!((v)= *(e))){(n)+=INT_SZ;continue;}else for((c)=0;(c)<INT_SZ;(c)+=BYTE_SZ,(v)>>=BYTE_SZ,(n)+= *(++(p)))for((p)=bitspos[(v)&0xff];*(p)!= -1 &&(((n)+= *(p)++)+1);)
#define		BIT_DO(n,bs) {register BLOCK zb=(BLOCK)I_GET(bs),zbp,zbe;register LONG zv,zc,*zp;BIT_LOOP(n,zbp,zbe,zb,zv,zc,zp){
#define		BIT_END }}
#define		FUNC_LOOP(ip,f)	for(ip=(f)->arr;ip<(f)->arr+(f)->arr_size;ip++)
#define		FUNC_LOOP2(e1,e2,f1,f2)	for(e1=(f1)->arr,e2=(f2)->arr;(e1<((f1)->arr + (f1)->arr_size)) && (e2 < ((f2)->arr + (f2)->arr_size));e1++,e2++)
#define         LIST_LOOP(e,l) for(e=l;e;e=e->next)
#define         LIST_LOOP2(e1,e2,l1,l2)  for(e1=l1,e2=l2; e1 && e2; e1=e1->next,e2=e2->next)
#define         LIST_LOOP3(e1,e2,e3,l1,l2,l3)  for(e1=l1,e2=l2,e3=l3; e1 && e2 && e3; e1=e1->next,e2=e2->next,e3=e3->next)
#define		PENL_LOOP(e, l) for(e = l ; e->next ; e = e->next)
#define		LIST_DO(i,l) {register LIST ze;LIST_LOOP(ze,(LIST)I_GET(l)){i=L_GET(ze);
#define		LIST_END }}
#define		AR_LOOP(p,e,a)	for((p)=(a)+1,(e)=(a)+ *(a);(p)<=(e);(p)++)
#define         L_GET(l)       ((l)->pres)
#define         I_GET(i)       ((i)->obj)
#define         I_ASSIGN(i,val)       (((i)->obj)=(LONG)val)
#define		P_GET(p)	((p)->t)
#define		LISTP_LOOP(lp,l)	for(lp= ((LIST *)&((l)->obj));*(lp);lp= &((*(lp))->next))
#define		ITMEQ(i1,i2)	(!i_cmp(i1,i2))
#define		L_TERM(lp,lpp)	(lpp=l_end(i_inc(L_GET(lp)),lpp))
#define		HOF(l)		((l)->pres)
#define		TOF(l)		((l)->next)
#define		I_NINC(i)	(((LONG)I_GET(i))++)
#define		I_NINC1(i)	((LONG)((i)->obj)++)
#define		L_EMPTY		(i_create('l',(POINTER)NULL))
#define		B_EMPTY		(i_create('b',(POINTER)b_create(1l)))
#define		Y_EMPTY		(i_create('y',(POINTER)ar_create(2l)))
#define		Y_PUSH(v,y)	(ar_push(v,(unsigned long int **)&I_GET(y)))
#define		Y_POP(y)	(ar_pop((unsigned long int *)I_GET(y)))
#define		Y_ELEM(e,y)	(*(((unsigned long int *)I_GET(y))+(e)+2l))
#define		I_INT(n)	(i_create('i',(POINTER)(n)))
#define		I_INC(i)	((i)->usage)++
#define		I_DEC(i)	((i)->usage)--
#define		L_EMPTYQ(l)	((LIST)I_GET(l) == (LIST)NULL)
#define		L_LAST(l)	((LIST *)&(I_GET(l)))
#define		FSYM(a)		((LONG)I_GET(((FUNC)I_GET(a))->arr[0]))
#define		i_sort(l)	i_sortc((l),i_cmp)
#define		ct_vars(t)	ct_terms((t),TRUE,FALSE)
#define		PT(p,t)		(((p)<<16)|(t))
#define		HPT(p,t)	((((p)&0x1f)<<5)|((t)&0x1f))
#define		TNO(pt)		((pt)&0xffff)
#define		PNO(pt)		((pt)>>16)
#define		GETPT(ip)	(*(++(ip)))
#define		FNDPT(p,t,pt)	for((pt)= *(hpt+HPT(p,t))+1;*(pt)!=PT(p,t);(pt)+=2)

/*
 * #######################################################################
 */

struct item {
	char item_type;			/* Can be	string ('s') */
					/*		atom ('a') */
					/*		integer ('i') */
					/*		real ('r') */
					/*		list ('l') */
					/*		functor ('f') */
					/*		hashed (prolog) name ('h') */
					/*		prolog variable ('v') */
					/*		integer array ('y') */
	unsigned short int usage;	/* Usage count */
	POINTER obj;
	unsigned long int extra;	/* Used for storing path/term info */
};

struct lmem {			/* List member */
        ITEM pres;		/* Present item */
        LIST next;		/* Next in the list */
};

#define		BLCK_SZ 4l	/* 4 integers in a bit array block */
#define		INT_SZ 32l	/* VAX has 32 bits in an unsigned long int */
#define		LOG_INT_SZ 5l	/* VAX has 32 bits in an unsigned long int */
#define		NBBL_SZ	4l	/* 4 bits in a nibble */
#define		BYTE_SZ	8l	/* 4 bits in a nibble */
#define		BYTE_RNG 256l

struct functor {
	LONG arr_size;
	ITEM *arr;
};

struct com {
	STRING pattern;
	LONG nargs;
	PREDICATE (*func) ();
	STRING helpmsg;
};

struct hashfns {
	PREDICATE (*eq) ();
	LONG (*hfn) ();
};

struct filerec {
	STRING filename;
	FILE *file;
	char buf[BUFSIZE+LBUF];
	STRING bufp;
	STRING buflim;
	LONG line_no;
};

struct otree {
	LONG val;
	LONG nleft;
	struct otree *left;
	struct otree *right;
};

#include        "ext_fn.h"
#include        "ext_var.h"
