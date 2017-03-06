############################################################################
#
#			GOLEM Makefile
#
############################################################################

.SUFFIXES: .pl .cmp
LDFLAGS= -O2 # -lm
CFLAGS=  -O2 # -g -pg -f68881
OBJECTS= main.o plg.o command.o init.o hash.o func.o set.o \
	item.o list.o utils.o alloc.o terms.o clause.o \
	integrat.o cost.o bits.o reduce.o determin.o pt.o \
	subduce.o control.o blits.o sample.o patch.o invent.o
SOURCE= main.c plg.c command.c init.c hash.c func.c set.c \
	item.c list.c utils.c alloc.c terms.c clause.c \
	integrat.c cost.c bits.c reduce.c determin.c pt.c \
	subduce.c control.c blits.c sample.c patch.c invent.c

golem: $(OBJECTS)
	cc $(CFLAGS) $(OBJECTS) -o golem $(LDFLAGS)
mem:
	touch item.c init.c plg.c
	make golem
count:
	wc $(SOURCE)
clean:
	 -rm -f *.o
