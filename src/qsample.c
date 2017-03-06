#include <stdio.h>
#define		RAND		rand()
#define		SRAND(x)	srand(x)
#define 	MYRAND(lo,hi) ((RAND%(((hi)-(lo))+1))+(lo))
#define		FALSE	0
#define		TRUE	1

main(argc,argv)
	int argc;
	char *argv[];
	{
	int samplesize,nlines=0,newline=TRUE,printing=FALSE,
		comment=FALSE,start=cputime();
	FILE *in,*out;
	char *inname,*outname;
	char c;
	if(argc!=4) {
		printf("Command should have form <qsample N FromFile ToFile>\n");
		exit(0);
	}
	sscanf(argv[1],"%d",&samplesize);
	inname=argv[2]; outname=argv[3];
	if (!(in=fopen(inname,"r"))) {
		printf("Cannot find %s\n",inname);
		exit(1);
	}
	out=fopen(outname,"w");
	printf("Counting number of lines\n");
	while((c=fgetc(in))!=EOF) {
	    if(newline) {
		if(c=='%') comment=TRUE;
		newline=FALSE;
	    }
	    if(c=='\n') {
		if(!comment) nlines++;
		newline=TRUE;
		comment=FALSE;
	    }
	}
	printf("Counted %d lines\n",nlines);
	fclose(in); in=fopen(inname,"r");
	printf("Sampling %d from %d\n",samplesize,nlines);
	newline=TRUE; comment=FALSE; printing=FALSE;
	while((c=fgetc(in))!=EOF) {
	    if(newline) {
		if(c=='%') {printing=FALSE; comment=TRUE;}
		else if(MYRAND(0,nlines)<=samplesize) {
		    printing=TRUE;
		    samplesize--;
		}
		else printing=FALSE;
		newline=FALSE;
	    }
	    if(printing) fputc(c,out);
	    if(c=='\n') {
		if(!comment) nlines--;
		newline=TRUE;
		comment=FALSE;
	    }
	}
	fclose(in); fclose(out);
	printf("Time taken = %dms\n",cputime()-start);
}

#include <sys/types.h>
#include <sys/times.h>
#include <sys/time.h>

int
cputime()
	{
	struct tms buffer;
	times(&buffer);
	return((buffer.tms_stime+buffer.tms_utime)*16.6);
}
