/* ####################################################################### */

/*                      GOLEM Utility Routines                		   */
/*                   	--------------------- 		                   */

/* ####################################################################### */

#include <stdio.h>
#include <signal.h>
#include <string.h>
#include "golem.h"

/*  d_error(msg) - error messages for GOLEM, prints message
 *	and forces a core dump.
 */

int
d_error(mesg)
        char *mesg;  {

        fprintf(stderr, "\n*** GOLEM Error\n");
        fprintf(stderr, "*** %s\n", mesg);
#ifdef SUNCHECK
	kill(getpid(),SIGQUIT);
	for(;;);
#else
	exit(1);
#endif
}

/*  strsave(s) - allocate space, save char *s, and return a pointer to s
 *   return NULL if no space is found
 */

STRING
strsave(s)
        char *s; {
        char *p;
	LONG length;

	length=strlen(s)+1;
        if ((p = (char *)GOLEM_CALLOC(length,sizeof(char),"strsave")) != NULL)
                strcpy(p, s);
        else
                d_error("strsave: GOLEM_CALLOC error (no space?)\n");

        return(p);
}

/* ualphanum(name) - checks whether name contains
 *	only alphanumeric characters starting with upper case letter
 */

PREDICATE
ualphanum(name)
	STRING name;
	{
	register STRING sp;
	
	if (*name == '\0' || !(UPCASE(*name)||*name=='_')) return(FALSE);
	STR_LOOP(sp,name+1) if (!ALPHANUM(*sp)) return(FALSE);
	return(TRUE);
}

/* lalphanum(name) - checks whether name contains
 *	only alphanumeric characters starting with lower case letter
 */

PREDICATE
lalphanum(name)
	STRING name;
	{
	register STRING sp;
	
	if (*name == '\0' || !LOWCASE(*name)) return(FALSE);
	STR_LOOP(sp,name+1) if (!ALPHANUM(*sp)) return(FALSE);
	return(TRUE);
}

/* number(name) - checks whether "name" is a number. Uses simple
 *	finite state parser.
 */

#define	SIGN	0l
#define	WHOL	1l
#define	FRAC	2l
#define	EXPN	3l

PREDICATE
number(name)
	STRING name;
	{
	LONG i;
	float f;
	LONG state=SIGN;
	STRING strp;
	register char c;
	STR_LOOP(strp,name) {
	  c= *strp;
	  switch(state) {
	    case SIGN:
	      if(DIGIT(c)) state=WHOL;
	      else if((c=='+'||c=='-')&& *(strp+1)!='\0') state=WHOL;
	      else return(FALSE);
	      break;
	    case WHOL:
	      if(c=='.') state=FRAC;
	      else if(!DIGIT(c)) return(FALSE);
	      break;
	    case FRAC:
	      if((c=='e'||c=='E')&& *(strp+1)!='\0') state=EXPN;
	      else if(!DIGIT(c)) return(FALSE);
	      break;
	    case EXPN:
	      if(!DIGIT(c)) return(FALSE);
	      break;
	    default:
	      return(FALSE);
	  }
	}
	if(state==SIGN) return(FALSE);
	else return(TRUE);
}

/* lsymbol(name) - checks whether name contains
 *	only Prolog non-alphanumeric printable characters
 */

PREDICATE
lsymbol(name)
	STRING name;
	{
	register STRING sp;
	if (*name == '\0') return(FALSE);
	STR_LOOP(sp,name)
		switch(*sp) {
		    case '+': case '-': case '*': case '/': case '\\': case '^':
		    case '<': case '>': case '=': case '`': case '~': case ':':
		    case '.': case '?': case '@': case '#': case '$': case '&': 
			break;
		    default:
			return(FALSE);
		}
	return(TRUE);
}

/* fsym(pair,name,arity) - pair should be term of type F/Arity.
 *	Assigns name and arity and returns hashed symbol number.
 */

LONG
fsym(pair,name,arity)
	ITEM pair;
	STRING *name;
	LONG *arity;
	{
	if(pair->item_type == 'f') {
	    if((LONG)I_GET(F_ELEM(0l,pair))!=pdiv ||
			F_ELEM(1l,pair)->item_type!='h' ||
			F_ELEM(2l,pair)->item_type!='i') {
		    return((LONG)I_ERROR);
	    }
	    *name=QP_ntos((LONG)I_GET(F_ELEM(1l,pair)));
	    *arity=(LONG)I_GET(F_ELEM(2l,pair));
	}
	else if(pair->item_type == 'h') {
	    *name=QP_ntos((LONG)I_GET(pair));
	    *arity=0l;
	}
	else return((LONG)I_ERROR);
	return(QP_ston(*name,*arity));
}

/* cputime() - returns cputime since start of process in ms.
 */

#ifdef SUNCHECK
#include <sys/types.h>
#include <sys/times.h>
#include <sys/time.h>
#else
#include <time.h>
#endif

LONG
cputime()
	{
#ifdef SUNCHECK
	struct tms buffer;
	times(&buffer);
	return((buffer.tms_stime+buffer.tms_utime)*16.6);

#else
	time_t timenow;
	time(&timenow);
	return(timenow*1000);
#endif
}

/* datetime() - returns no. of seconds since 1.1.1970
 */

LONG
datetime()
	{
#ifdef SUNCHECK
	struct timeval tp;
	struct timezone tzp;
	gettimeofday(&tp,&tzp);
	return(tp.tv_sec);
#else
	return(0);
#endif
}

/* g_message(s,a0,..,a9) - same argument pattern as printf but
 *	only prints s if the debug flag is set.
 */

int
g_message(s,a0,a1,a2,a3,a4,a5,a6,a7,a8,a9)
	STRING s;
	POINTER a0,a1,a2,a3,a4,a5,a6,a7,a8,a9;
	{
	char mess[MAXMESS];
	sprintf(mess,"[%s]\n",s);
	if(debug) printf(mess,a0,a1,a2,a3,a4,a5,a6,a7,a8,a9);
}
