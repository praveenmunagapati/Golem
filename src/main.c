/* ####################################################################### */

/*			GOLEM main functions				   */
/*			--------------------				   */

/* ####################################################################### */

#include <stdio.h>
#include "golem.h"

FILEREC *ttyin;
FILEREC *ttyout;
PREDICATE interactive=TRUE;
ITEM fileroot=(ITEM)NULL;
PREDICATE c_doall();

#ifdef SUNCHECK
main(argc,argv)
	LONG argc;
	STRING argv[];
	{
#ifdef	CHECK_SECURITY
	check_security();
#endif
	c_open();
	checkargs(argc,argv);
	if(interactive) main_prompt();
	else c_doall(fileroot);
	c_close();
}
#else
main()
	{
#ifdef	CHECK_SECURITY
	check_security();
#endif
	c_open();
	main_prompt();
	c_close();
}
#endif

/*
 * checkargs/2 - expects command line
 *	golem [-i] fileroot
 */

checkargs(argc,argv)
	LONG argc;
	STRING argv[];
	{
	LONG argno;
	STRING sp;
	for(argno=1;argno<argc;argno++) {
	    if(*argv[argno] == '-') {
		STR_LOOP(sp,argv[argno]+1)
		    switch(*sp) {
			case 'i': /* Interactive */
			    interactive=TRUE;
			    break;
			case 'd': /* Debug flag */
			    c_debug();
			    break;
			default:
			    printf("[Unrecognised flag option <%c>]\n",*sp);
		    }
	    }
	    else if (fileroot==(ITEM)NULL) {
		fileroot=i_create('h',(POINTER)QP_ston(argv[argno],0l));
		interactive=FALSE;
	    }
	    else printf("[Ignoring additional file <%s>]\n",argv[argno]);
	}
}
