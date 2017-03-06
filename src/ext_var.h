
/* ####################################################################### */

/*              GOLEM Include File for External Variables		   */
/*              -----------------------------------------		   */

/* ####################################################################### */

#ifdef MEMCHECK
extern ITEM all_items;
#endif

extern LONG memout;
extern LONG pdot;	/* Hashed symbol value of ./2 */
extern LONG pempty;	/* Hashed symbol value of [] */
extern LONG pminus;	/* Hashed symbol value of -/0 */
extern LONG pplus;	/* Hashed symbol value of +/0 */
extern LONG pif;	/* Hashed symbol value of ':-'/0 */
extern LONG pcomma;	/* Hashed symbol value of ','/0 */
extern LONG pdot0;	/* Hashed symbol value of '.'/0 */
extern LONG pdiv;	/* Hashed symbol value of '/'/2 */
extern LONG peof;	/* Hashed symbol value of end_of_file/0 */
extern FILEREC *ttyin;
extern FILEREC *ttyout;
extern struct hashfns superhash[];
extern ITEM varno;	/* the next variable number */
extern ITEM pts;	/* Path->terms array */
extern ITEM pas;	/* Path->atoms array */
extern ITEM tps;	/* Term->paths array */
extern ITEM ptas;	/* Path/term->atoms array */
extern ITEM ops;	/* Operators */
extern ITEM bbacks;	/* The bitset of background ground atoms */
extern ITEM bfores;	/* The bitset of foreground ground atoms */
extern ITEM bnegs;	/* The bitset of negative examples */
extern ITEM rules;	/* The rulebase (Horn clauses) */
extern ITEM spsyms;	/* Super-set of predicate/function symbols */
extern ITEM spatoms;	/* Super-set of atoms */
extern ITEM sppaths;	/* Super-set of paths */
extern ITEM spterms;	/* Super-set of terms */
extern ITEM asz;	/* Atoms sizes */
extern ITEM modes;	/* Hash table of mode declarations */
extern ITEM determs;	/* Hash table of determinations */
extern ITEM nondeterm;	/* Bitset of Non-determinate predicates */
extern ITEM pathio;	/* Array mapping paths to IO mode */
extern ITEM predatoms;	/* Predicate to atoms mapping */
extern ITEM hypothesis;	/* A clause */
extern LONG *hpt[];	/* Fast hash table determines path-term no. */
extern LONG vlim,exlim,dtlim,noiselim,smlim;
extern LONG ptno;	/* Path/term number */
extern LONG bitspos[BYTE_RNG] [10];
			/* Bit increment table */
extern unsigned char byte_sz[BYTE_RNG];
extern unsigned char log2[BYTE_RNG]; /* Log table */
extern PREDICATE debug;	/* Debug flag */
extern PREDICATE interactive; /* Interactive session? */
extern LONG charlast; /* Used for printing terms */
extern ITEM fileroot;	/* Root name for golem file I/O */
extern ITEM substats;	/* Subduction statistics */
extern PREDICATE dostats; /* Save stats during clause execution? */
