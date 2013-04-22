\datethis
@*Intro. This program is part of a series of ``SAT-solvers'' that I'm putting
together for my own education as I prepare to write Section 7.2.2.2 of
{\sl The Art of Computer Programming}. My intent is to have a variety of
compatible programs on which I can run experiments to learn how different
approaches work in practice.

I wrote it just after reading the classic paper by Davis, Logemann, and
Loveland [{\sl CACM\/ \bf5} (1962), 394--397] for the first time;
that's the paper where the first decent implementation of a SAT-solver
is discussed. The authors don't explain their data structures in enough
detail for me to reconstruct them, but they describe a procedure rather
like {\mc SAT0} --- with an important extension. My {\mc SAT0} assigns values
to the variables strictly in sequence, while theirs realizes early on
that certain variables have forced values. Namely, every clause
with only one literal forces that literal to be true; and every variable
that occurs only positively or only negatively can be forced to
be positive or negative without affecting satisfiability. They put
such variables on a ``ready list,'' and deduce the consequences of all such
forced moves before making any choices that lead to two-way branching.

Thus, the present program {\mc SAT3} is an example of what happens
when {\mc SAT0} is extended with such a ``ready list.''

If you have already read {\mc SAT0} (or some other program of this
series), you might as well skip now past all the code for the
``I/O wrapper,'' because you have seen it before.

The input on |stdin| is a series of lines with one clause per line. Each
clause is a sequence of literals separated by spaces. Each literal is
a sequence of one to eight ASCII characters between \.{!} and \.{\}},
inclusive, not beginning with \.{\~},
optionally preceded by \.{\~} (which makes the literal ``negative'').
For example, Rivest's famous clauses on four variables,
found in 6.5--(13) and 7.1.1--(32) of {\sl TAOCP}, can be represented by the
following eight lines of input: 
$$\chardef~=`\~
\vcenter{\halign{\tt#\cr
x2 x3 ~x4\cr
x1 x3 x4\cr
~x1 x2 x4\cr
~x1 ~x2 x3\cr
~x2 ~x3 x4\cr
~x1 ~x3 ~x4\cr
x1 ~x2 ~x4\cr
x1 x2 ~x3\cr}}$$
Input lines that begin with \.{\~\ } are ignored (treated as comments).
The output will be `\.{\~}' if the input clauses are unsatisfiable.
Otherwise it will be a list of noncontradictory literals that cover each
clause, separated by spaces. (``Noncontradictory'' means that we don't
have both a literal and its negation.) The input above would, for example,
yield `\.{\~}'; but if the final clause were omitted, the output would
be `\.{x1} \.{x2} \.{\~x3}', in some order, possibly together
with either \.{x4} or \.{\~x4} (but not both). No attempt is made to
find all solutions; at most one solution is given.

The running time in ``mems'' is also reported, together with the approximate
number of bytes needed for data storage. One ``mem'' essentially means a
memory access to a 64-bit word.
(These totals don't include the time or space needed to parse the
input or to format the output.)

@ So here's the structure of the program. (Skip ahead if you are
impatient to see the interesting stuff.)

@d o mems++ /* count one mem */
@d oo mems+=2 /* count two mems */
@d ooo mems+=3 /* count three mems */

@c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "gb_flip.h"
typedef unsigned int uint; /* a convenient abbreviation */
typedef unsigned long long ullng; /* ditto */
@<Type definitions@>;
@<Global variables@>;
@<Subroutines@>;
main (int argc, char *argv[]) {
  register uint c,h,i,j,k,l,p,q,r,level,kk,pp,qq,ll;
  @<Process the command line@>;
  @<Initialize everything@>;
  @<Input the clauses@>;
  if (verbose&show_basics)
    @<Report the successful completion of the input phase@>;
  @<Set up the main data structures@>;
  imems=mems, mems=0;
  @<Solve the problem@>;
  if (verbose&show_basics)
    fprintf(stderr,"Altogether %llu+%llu mems, %llu bytes.\n",
                     imems,mems,bytes);
}

@ @d show_basics 1 /* |verbose| code for basic stats */
@d show_choices 2 /* |verbose| code for backtrack logging */
@d show_details 4 /* |verbose| code for further commentary */
@d show_unused_vars 8 /* |verbose| code to list variables not in solution */

@<Glob...@>=
int random_seed=0; /* seed for the random words of |gb_rand| */
int verbose=show_basics+show_unused_vars; /* level of verbosity */
int hbits=8; /* logarithm of the number of the hash lists */
int buf_size=1024; /* must exceed the length of the longest input line */
FILE *out_file; /* file for optional output */
char *out_name; /* its name */
ullng imems,mems; /* mem counts */
ullng bytes; /* memory used by main data structures */
ullng thresh=0; /* report when |mems| exceeds this, if |delta!=0| */
ullng delta=0; /* report every |delta| or so mems */

@ On the command line one can say
\smallskip
\item{$\bullet$}
`\.v$\langle\,$integer$\,\rangle$' to enable various levels of verbose
 output on |stderr|;
\item{$\bullet$}
`\.h$\langle\,$positive integer$\,\rangle$' to adjust the hash table size;
\item{$\bullet$}
`\.b$\langle\,$positive integer$\,\rangle$' to adjust the size of the input
buffer; and/or
\item{$\bullet$}
`\.s$\langle\,$integer$\,\rangle$' to define the seed for any random numbers
that are used.
\item{$\bullet$}
`\.d$\langle\,$integer$\,\rangle$' to set |delta| for periodic state reports.
\item{$\bullet$}
`\.x$\langle\,$filename$\,\rangle$' to copy the input plus a
solution-eliminating clause to the specified file. If the given problem is
satisfiable in more than one way, a different solution can be obtained by
inputting that file.

@<Process the command line@>=
for (j=argc-1,k=0;j;j--) switch (argv[j][0]) {
case 'v': k|=(sscanf(argv[j]+1,"%d",&verbose)-1);@+break;
case 'h': k|=(sscanf(argv[j]+1,"%d",&hbits)-1);@+break;
case 'b': k|=(sscanf(argv[j]+1,"%d",&buf_size)-1);@+break;
case 's': k|=(sscanf(argv[j]+1,"%d",&random_seed)-1);@+break;
case 'd': k|=(sscanf(argv[j]+1,"%lld",&delta)-1);@+thresh=delta;@+break;
case 'x': out_name=argv[j]+1, out_file=fopen(out_name,"w");
  if (out_file) break;
  fprintf(stderr,"I can't open file `%s' to output!\n",out_name);
   /* fall through */
default: k=1; /* unrecognized command-line option */
}
if (k || hbits<0 || hbits>30 || buf_size<=0) {
  fprintf(stderr,
     "Usage: %s [v<n>] [h<n>] [b<n>] [s<n>] [d<n>] [x<foo>]\n",argv[0]);
  exit(-1);
}

@*The I/O wrapper. The following routines read the input and absorb it into
temporary data areas from which all of the ``real'' data structures
can readily be initialized. My intent is to incorporate these routines in all
of the SAT-solvers in this series. Therefore I've tried to make the code
short and simple, yet versatile enough so that almost no restrictions are
placed on the sizes of problems that can be handled. These routines are
supposed to work properly unless there are more than
$2^{32}-1=4$,294,967,295 occurrences of literals in clauses,
or more than $2^{31}-1=2$,147,483,647 variables or clauses.

In these temporary tables, each variable is represented by four things:
its unique name; its serial number; the clause number (if any) in which it has
most recently appeared; and a pointer to the previous variable (if any)
with the same hash address. Several variables at a time
are represented sequentially in small chunks of memory called ``vchunks,''
which are allocated as needed (and freed later).

@d vars_per_vchunk 341 /* preferably $(2^k-1)/3$ for some $k$ */

@<Type...@>=
typedef union {
  char ch8[8];
  uint u2[2];
  long long lng;
} octa;
typedef struct tmp_var_struct {
  octa name; /* the name (one to seven ASCII characters) */
  uint serial; /* 0 for the first variable, 1 for the second, etc. */
  int stamp; /* |m| if positively in clause |m|; |-m| if negatively there */
  struct tmp_var_struct *next; /* pointer for hash list */
} tmp_var;
@#
typedef struct vchunk_struct {
  struct vchunk_struct *prev; /* previous chunk allocated (if any) */
  tmp_var var[vars_per_vchunk];
} vchunk;

@ Each clause in the temporary tables is represented by a sequence of
one or more pointers to the |tmp_var| nodes of the literals involved.
A negated literal is indicated by adding~1 to such a pointer.
The first literal of a clause is indicated by adding~2.
Several of these pointers are represented sequentially in chunks
of memory, which are allocated as needed and freed later.

@d cells_per_chunk 511 /* preferably $2^k-1$ for some $k$ */

@<Type...@>=
typedef struct chunk_struct {
  struct chunk_struct *prev; /* previous chunk allocated (if any) */
  tmp_var *cell[cells_per_chunk];
} chunk;

@ @<Glob...@>=
char *buf; /* buffer for reading the lines (clauses) of |stdin| */
tmp_var **hash; /* heads of the hash lists */
uint hash_bits[93][8]; /* random bits for universal hash function */
vchunk *cur_vchunk; /* the vchunk currently being filled */
tmp_var *cur_tmp_var; /* current place to create new |tmp_var| entries */
tmp_var *bad_tmp_var; /* the |cur_tmp_var| when we need a new |vchunk| */
chunk *cur_chunk; /* the chunk currently being filled */
tmp_var **cur_cell; /* current place to create new elements of a clause */
tmp_var **bad_cell; /* the |cur_cell| when we need a new |chunk| */
ullng vars; /* how many distinct variables have we seen? */
ullng clauses; /* how many clauses have we seen? */
ullng nullclauses; /* how many of them were null? */
ullng cells; /* how many occurrences of literals in clauses? */

@ @<Initialize everything@>=
gb_init_rand(random_seed);
buf=(char*)malloc(buf_size*sizeof(char));
if (!buf) {
  fprintf(stderr,"Couldn't allocate the input buffer (buf_size=%d)!\n",
            buf_size);
  exit(-2);
}
hash=(tmp_var**)malloc(sizeof(tmp_var)<<hbits);
if (!hash) {
  fprintf(stderr,"Couldn't allocate %d hash list heads (hbits=%d)!\n",
           1<<hbits,hbits);
  exit(-3);
}
for (h=0;h<1<<hbits;h++) hash[h]=NULL;

@ The hash address of each variable name has $h$ bits, where $h$ is the
value of the adjustable parameter |hbits|.
Thus the average number of variables per hash list is $n/2^h$ when there
are $n$ different variables. A warning is printed if this average number
exceeds 10. (For example, if $h$ has its default value, 8, the program will
suggest that you might want to increase $h$ if your input has 2560
different variables or more.)

All the hashing takes place at the very beginning,
and the hash tables are actually recycled before any SAT-solving takes place;
therefore the setting of this parameter is by no means crucial. But I didn't
want to bother with fancy coding that would determine $h$ automatically.

@<Input the clauses@>=
while (1) {
  if (!fgets(buf,buf_size,stdin)) break;
  clauses++;
  if (buf[strlen(buf)-1]!='\n') {
    fprintf(stderr,
      "The clause on line %d (%.20s...) is too long for me;\n",clauses,buf);
    fprintf(stderr," my buf_size is only %d!\n",buf_size);
    fprintf(stderr,"Please use the command-line option b<newsize>.\n");
    exit(-4);
  }
  @<Input the clause in |buf|@>;
}
if ((vars>>hbits)>=10) {
  fprintf(stderr,"There are %d variables but only %d hash tables;\n",
     vars,1<<hbits);
  while ((vars>>hbits)>=10) hbits++;
  fprintf(stderr," maybe you should use command-line option h%d?\n",hbits);
}
clauses-=nullclauses;
if (vars>=0x80000000) {
  fprintf(stderr,"Whoa, the input had %llu variables!\n",cells);
  exit(-664);
}
if (clauses>=0x80000000) {
  fprintf(stderr,"Whoa, the input had %llu clauses!\n",cells);
  exit(-665);
}
if (cells>=0x100000000) {
  fprintf(stderr,"Whoa, the input had %llu occurrences of literals!\n",cells);
  exit(-666);
}

@ @<Input the clause in |buf|@>=
for (j=k=0;;) {
  while (buf[j]==' ') j++; /* scan to nonblank */
  if (buf[j]=='\n') break;
  if (buf[j]<' ' || buf[j]>'~') {
    fprintf(stderr,"Illegal character (code #%x) in the clause on line %d!\n",
      buf[j],clauses);
    exit(-5);
  }
  if (buf[j]=='~') i=1,j++;
  else i=0;
  @<Scan and record a variable; negate it if |i==1|@>;
}
if (k==0) {
  fprintf(stderr,"(Empty line %d is being ignored)\n",clauses);
  nullclauses++; /* strictly speaking it would be unsatisfiable */
}
goto clause_done;
empty_clause: @<Remove all variables of the current clause@>;
clause_done: cells+=k;

@ We need a hack to insert the bit codes 1 and/or 2 into a pointer value.

@d hack_in(q,t) (tmp_var*)(t|(ullng)q)

@<Scan and record a variable; negate it if |i==1|@>=
{
  register tmp_var *p;
  if (cur_tmp_var==bad_tmp_var) @<Install a new |vchunk|@>;
  @<Put the variable name beginning at |buf[j]| in |cur_tmp_var->name|
     and compute its hash code |h|@>;
  @<Find |cur_tmp_var->name| in the hash table at |p|@>;
  if (p->stamp==clauses || p->stamp==-clauses) @<Handle a duplicate literal@>@;
  else {
    p->stamp=(i? -clauses: clauses);
    if (cur_cell==bad_cell) @<Install a new |chunk|@>;
    *cur_cell=p;
    if (i==1) *cur_cell=hack_in(*cur_cell,1);
    if (k==0) *cur_cell=hack_in(*cur_cell,2);
    cur_cell++,k++;
  }
}

@ @<Install a new |vchunk|@>=
{
  register vchunk *new_vchunk;
  new_vchunk=(vchunk*)malloc(sizeof(vchunk));
  if (!new_vchunk) {
    fprintf(stderr,"Can't allocate a new vchunk!\n");
    exit(-6);
  }
  new_vchunk->prev=cur_vchunk, cur_vchunk=new_vchunk;
  cur_tmp_var=&new_vchunk->var[0];
  bad_tmp_var=&new_vchunk->var[vars_per_vchunk];
}  

@ @<Install a new |chunk|@>=
{
  register chunk *new_chunk;
  new_chunk=(chunk*)malloc(sizeof(chunk));
  if (!new_chunk) {
    fprintf(stderr,"Can't allocate a new chunk!\n");
    exit(-7);
  }
  new_chunk->prev=cur_chunk, cur_chunk=new_chunk;
  cur_cell=&new_chunk->cell[0];
  bad_cell=&new_chunk->cell[cells_per_chunk];
}  

@ The hash code is computed via ``universal hashing,'' using the following
precomputed tables of random bits.

@<Initialize everything@>=
for (j=92;j;j--) for (k=0;k<8;k++)
  hash_bits[j][k]=gb_next_rand();

@ @<Put the variable name beginning at |buf[j]| in |cur_tmp_var->name|...@>=
cur_tmp_var->name.lng=0;
for (h=l=0;buf[j+l]>' '&&buf[j+l]<='~';l++) {
  if (l>7) {
    fprintf(stderr,
        "Variable name %.9s... in the clause on line %d is too long!\n",
        buf+j,clauses);
    exit(-8);
  }
  h^=hash_bits[buf[j+l]-'!'][l];
  cur_tmp_var->name.ch8[l]=buf[j+l];
}
if (l==0) goto empty_clause; /* `\.\~' by itself is like `true' */
j+=l;
h&=(1<<hbits)-1;

@ @<Find |cur_tmp_var->name| in the hash table...@>=
for (p=hash[h];p;p=p->next)
  if (p->name.lng==cur_tmp_var->name.lng) break;
if (!p) { /* new variable found */
  p=cur_tmp_var++;
  p->next=hash[h], hash[h]=p;
  p->serial=vars++;
}

@ The most interesting aspect of the input phase is probably the ``unwinding''
that we might need to do when encountering a literal more than once
in the same clause.

@<Handle a duplicate literal@>=
{
  if ((p->stamp>0)==(i>0)) goto empty_clause;
}

@ An input line that begins with `\.{\~\ }' is silently treated as a comment.
Otherwise redundant clauses are logged, in case they were unintentional.
(One can, however, intentionally
use redundant clauses to force the order of the variables.)

@<Remove all variables of the current clause@>=
while (k) {
  @<Move |cur_cell| backward to the previous cell@>;
  k--;
}
if ((buf[0]!='~')||(buf[1]!=' '))
  fprintf(stderr,"(The clause on line %d is always satisfied)\n",clauses);
nullclauses++;

@ @<Move |cur_cell| backward to the previous cell@>=
if (cur_cell>&cur_chunk->cell[0]) cur_cell--;
else {
  register chunk *old_chunk=cur_chunk;
  cur_chunk=old_chunk->prev;@+free(old_chunk);
  bad_cell=&cur_chunk->cell[cells_per_chunk];
  cur_cell=bad_cell-1;
}

@ @<Move |cur_tmp_var| backward to the previous temporary variable@>=
if (cur_tmp_var>&cur_vchunk->var[0]) cur_tmp_var--;
else {
  register vchunk *old_vchunk=cur_vchunk;
  cur_vchunk=old_vchunk->prev;@+free(old_vchunk);
  bad_tmp_var=&cur_vchunk->var[vars_per_vchunk];
  cur_tmp_var=bad_tmp_var-1;
}

@ @<Report the successful completion of the input phase@>=
fprintf(stderr,"(%d variables, %d clauses, %llu literals successfully read)\n",
                       vars,clauses,cells);

@*SAT solving, version 3. OK, now comes my hypothetical recreation of
of the Davis--Logemann--Loveland SAT solver.
The algorithm below essentially tries to solve a satisfiability problem
by having a ``to-do'' list of variables whose values haven't been assigned,
and a ``ready'' stack of variables whose values are no-brainers
if the remaining clauses are to be satisfied. If the ready stack is
empty but the to-do list is not, the first variable of the to-do list
is set to its most plausible value, and the same idea is used
recursively on the remaining $(n-1)$-variable
problem. If this doesn't work, we try the other possibility for
that variable, and the result will either succeed or fail.

Data structures to support that method should allow us to do the
following things easily:
\smallskip
\item{$\bullet$}Know, for each variable, the clauses in which
that variable occurs, and in how many of them it occurs positively
or negatively (two counts).
\item{$\bullet$}Know, for each clause, the literals that it currently
contains.
\item{$\bullet$}Delete literals from clauses when they don't satisfy it.
\item{$\bullet$}Delete clauses that have already been satisfied.
\item{$\bullet$}Insert deleted literals and/or clauses when
backing up to reconsider previous choices.
\item{$\bullet$}Maintain the to-do list and the ready stack.
\smallskip\noindent
The original clause sizes are known in advance. Therefore we can use a
combination of sequential and linked memory to accomplish all of these goals.
(However, I plan to try a less sequential, 2D-linked approach in future
experiments, comparing them with this version.)

@ The basic unit in our data structure is called a cell. There's one
cell for each literal in each clause, and there also are $3n+1$ special
cells explained below. Each nonspecial cell belongs to a doubly linked
list for the corresponding literal, as well as to a sequential list
for the relevant clause. It also ``knows'' the number of its clause
and the number of its literal (which is $2k$ or $2k+1$ for the
positive and negative versions of variable~$k$).

Each link is a 32-bit integer. (I don't use \CEE/ pointers in the main
data structures, because they occupy 64 bits and clutter up the caches.)
The integer is an index into a monolithic array of cells called |mem|.

@<Type...@>=
typedef struct {
  uint flink,blink; /* forward and backward links for this literal */
  uint owner; /* clause number, or size in the special list-head cells */
  uint litno; /* literal number */
} cell;

@ Each clause is represented by a pointer to its first cell and by its
current size. My first draft of this program also included links to the
preceding and following cells, in a doubly linked cyclic list
of all the active clauses that are currently active; but later I realized
that such a list is irrelevant, so it might as well be immaterial.

@<Type...@>=
typedef struct {
  uint start; /* the address in |mem| where the cells for this clause start */
  uint size; /* the current number of literals in this clause */
} clause;

@ If there are $n$ variables, there are $2n$ possible literals. Hence we
reserve $2n$ special cells at the beginning of |mem|, for the heads of
the lists that link all occurrences of the same literal together.

The lists for variable $k$ begin in locations $2k$ and $2k+1$, corresponding to
its positive and negative incarnations, for $0\le k<n$. The |owner| field
in the list head tells the total size of the list, so we sometimes
call it |listsize|.

A variable also can belong to either the to-do list or the ready stack.
The links for variable $k$ in those lists are in special cell $2n+k$,
for $0\le k<n$. The |owner| field in that cell is nonzero if and only if
$k$ is on the ready stack; and such a case, |owner| points to the
next ready variable, if any, so we use the symbolic name |ready_link|
instead of |owner| in this context. The |ready_link| field at the
bottom of the ready stack is the nonzero value |ready_sentinel|.
The |litno| field of a variable on the ready stack indicates
whether the variable should be forced positive or negative.

Special cell $3n$ serves as a header node for the
to-do list and the ready stack.

A variable is also represented by its name, for purposes of output.
The name appears in a separate array |vmem| of vertex nodes.

@d listsize owner /* alternative name for the |owner| field */
@d ready_link owner /* another alternative name for that field */
@d ready_sentinel 1 /* an arbitrary (but nonzero) constant */
@d varcell(x) (vars+vars+(x)) /* address in |mem| of variable |x|'s cell */

@<Type...@>=
typedef struct {
  octa name; /* the variable's symbolic name */
} variable;

@ The backtracking process also has a sequential stack of state information.

@<Type...@>=
typedef struct {
  uint ready; /* current size of the ready stack */
  uint var; /* variable whose value is being set */
  uint move; /* code for what we're setting it */
} state;

@ @<Glob...@>=
cell *mem; /* the master array of cells */
uint nonspec; /* address in |mem| of the first non-special cell */
uint head; /* address in |mem| of the head of the to-do list and ready stack */
clause *cmem; /* the master array of clauses */
variable *vmem; /* the master array of variables */
state *smem; /* the stack of choices made so far */
uint active; /* the total number of active clauses */
uint ready; /* the total number of ready variables */

@ Here is a subroutine that prints a clause symbolically. It illustrates
some of the conventions of the data structures that have been explained above.
I use it only for debugging.

Incidentally, the clause numbers reported to the user after the input phase
may differ from the line numbers reported during the input phase,
when |nullclauses>0|.

@<Sub...@>=
void print_clause(uint c) {
  register uint k,l;
  printf("%d:",c); /* show the clause number */
  for (k=0;k<cmem[c].size;k++) {
    l=mem[cmem[c].start+k].litno;
    printf(" %s%.8s", l&1? "~": "", vmem[l>>1].name.ch8); /* $k$th literal */
  }
  printf("\n");
}

@ Similarly we can print out all of the clauses that use (or originally used)
a particular literal.

@<Sub...@>=
void print_clauses_for(int l) {
  register uint p;
  for (p=mem[l].flink;p>=nonspec;p=mem[p].flink)
    print_clause(mem[p].owner);
}

@ Speaking of debugging, here's a routine to check if the redundant
parts of our data structure have gone awry.

@<Sub...@>=
void sanity(void) {
  register uint k,l,c,i,p;
  for (k=mem[head].flink;k!=head;k=mem[k].flink) {
    if (mem[mem[k].blink].flink!=k)
      fprintf(stderr,"Variable list badly linked at %d!\n",k);
    if (k>head || k<vars+vars)
      fprintf(stderr,"Variable list entry %d out of bounds!\n",k);
    p=mem[k].ready_link;
    if (p>head || (p<vars+vars && p!=ready_sentinel))
      fprintf(stderr,"Ready list entry %d out of bounds!\n",k);
    for (i=0;i<2;i++) {
      l=((k-vars-vars)<<1)+i;
      for (p=mem[l].flink;p>=nonspec;p=mem[p].flink) {
        if (mem[mem[p].blink].flink!=p)
          fprintf(stderr,"Literal list badly linked at %d!\n",p);
        if (mem[p].litno!=l)
          fprintf(stderr,"Literal list %d shows wrong literal!\n",l);
        c=mem[p].owner;
        if (p<cmem[c].start || p>=cmem[c].start+cmem[c].size)
          fprintf(stderr,
            "Literal list entry %d out of bounds for clause %d!\n",p,c);
      }
      if (p!=l || mem[mem[p].flink].blink!=l)
          fprintf(stderr,"Literal list %d ends badly!\n",l);
      if (mem[l].listsize==0 && mem[k].ready_link==0)
          fprintf(stderr,"Variable %d should be ready!\n",l>>1);
    }
  }
}

@ In long runs it's helpful to know how far we've gotten.

@<Sub...@>=
void print_state(int l) {
  register int k;
  fprintf(stderr," after %lld mems:",mems);
  for (k=0;k<=l;k++) fprintf(stderr,"%c",smem[k].move+'0');
  fprintf(stderr,"\n");
  fflush(stderr);
}

@*Initializing the real data structures.
Okay, we're ready now to convert the temporary chunks of data into the
form we want, and to recycle those chunks. The code below is intended to be
a prototype for similar tasks in later programs of this series.

@<Set up the main data structures@>=
@<Allocate the main arrays@>;
@<Copy all the temporary cells to the |mem| and |cmem| arrays
   in proper format@>;
@<Copy all the temporary variable nodes to the |vmem| array in proper format@>;
@<Check consistency@>;
if (out_file) @<Copy all the clauses to |out_file|@>;

@ @<Allocate the main arrays@>=
free(buf);@+free(hash); /* a tiny gesture to make a little room */
head=vars+vars+vars;
nonspec=head+1;
if (nonspec+cells>=0x100000000) {
  fprintf(stderr,"Whoa, nonspec+cells is too big for me!\n");
  exit(-667);
}
mem=(cell*)malloc((nonspec+cells)*sizeof(cell));
if (!mem) {
  fprintf(stderr,"Oops, I can't allocate the big mem array!\n");
  exit(-10);
}
bytes=(nonspec+cells)*sizeof(cell);
cmem=(clause*)malloc((clauses+1)*sizeof(clause));
if (!cmem) {
  fprintf(stderr,"Oops, I can't allocate the cmem array!\n");
  exit(-11);
}
bytes+=(clauses+1)*sizeof(clause);
vmem=(variable*)malloc(vars*sizeof(variable));
if (!vmem) {
  fprintf(stderr,"Oops, I can't allocate the vmem array!\n");
  exit(-12);
}
bytes+=vars*sizeof(variable);
smem=(state*)malloc(vars*sizeof(state));
if (!smem) {
  fprintf(stderr,"Oops, I can't allocate the smem array!\n");
  exit(-13);
}
bytes+=vars*sizeof(state);

@ @<Copy all the temporary cells to the |mem| and |cmem| arrays...@>=
for (j=0;j<vars+vars;j++) o,mem[j].flink=0;
for (k=0;k<vars;k++)
  oo,mem[varcell(k)].flink=(k==vars-1? head: varcell(k+1)),
    mem[varcell(k)].blink=(k==0? head: varcell(k-1)),
    mem[varcell(k)].ready_link=0;
o,mem[head].flink=varcell(0), mem[head].blink=varcell(vars-1);
o,mem[head].ready_link=ready_sentinel;
for (c=clauses,j=nonspec; c; c--) {
  o,cmem[c].start=j,cmem[c].size=0;
  @<Insert the cells for the literals of clause |c|@>;
}
active=clauses;
@<Fix up the |blink| fields and compute the list sizes@>;
@<Sort the literals within each clause@>;

@ The basic idea is to ``unwind'' the steps that we went through while
building up the chunks.

@d hack_out(q) (((ullng)q)&0x3)
@d hack_clean(q) ((tmp_var*)((ullng)q&-4))

@<Insert the cells for the literals of clause |c|@>=
for (i=0;i<2;j++) {
  @<Move |cur_cell| back...@>;
  i=hack_out(*cur_cell);
  p=hack_clean(*cur_cell)->serial;
  p+=p+(i&1);
  ooo,mem[j].flink=mem[p].flink, mem[p].flink=j;
  o,mem[j].owner=c, mem[j].litno=p;
}

@ @<Fix up the |blink| fields and compute the list sizes@>=
for (k=0;k<vars+vars;k++) {
  for (o,i=0,q=k,p=mem[k].flink;p>=nonspec;i++,q=p,o,p=mem[p].flink)
    o,mem[p].blink=q;
  oo,mem[k].blink=q, mem[q].flink=k;
  o,mem[k].listsize=i, mem[k].litno=k;
}

@ The backtracking scheme we will use works nicely when the literals
of a clause are arranged so that the first one to be tried comes last.
Then a false literal is removed from its clause simply by decreasing
the clause's |size| field.

The following sorting scheme takes linear time, in the number of cells,
because of the characteristics of our data structures.

@<Sort the literals within each clause@>=
for (k=vars+vars-1;((int)k)>=0;k--)
  for (o,j=mem[k].flink;j>=nonspec;o,j=mem[j].flink) {
    o,c=mem[j].owner;
    o,i=cmem[c].size, p=cmem[c].start+i;
    if (j!=p)
      @<Swap cell |j| with cell |p|@>;
    o,cmem[c].size=i+1;
  }

@ Sometimes doubly linked lists make me feel good, even when spending 11 mems.
(For mem computation, |flink| and |blink| are assumed to be stored in
a single 64-bit word.)

@<Swap cell |j|...@>=
{
  o,q=mem[p].flink, r=mem[p].blink;
  oo,mem[p].flink=mem[j].flink, mem[p].blink=mem[j].blink;
  oo,mem[mem[j].flink].blink=mem[mem[j].blink].flink=p;
  o,mem[j].flink=q, mem[j].blink=r;
  oo,mem[q].blink=j, mem[r].flink=j;
  oo,mem[j].litno=mem[p].litno;
  o,mem[p].litno=k;
  j=p;
}

@ @<Copy all the temporary variable nodes to the |vmem| array...@>=
for (c=vars; c; c--) {
  @<Move |cur_tmp_var| back...@>;
  o,vmem[c-1].name.lng=cur_tmp_var->name.lng;
}

@ We should now have unwound all the temporary data chunks back to their
beginnings.

@<Check consistency@>=
if (cur_cell!=&cur_chunk->cell[0] ||
     cur_chunk->prev!=NULL ||
     cur_tmp_var!=&cur_vchunk->var[0] ||
     cur_vchunk->prev!=NULL) {
  fprintf(stderr,"This can't happen (consistency check failure)!\n");
  exit(-14);
}
free(cur_chunk);@+free(cur_vchunk);

@ @<Copy all the clauses to |out_file|@>=
{
  for (c=1;c<=clauses;c++) {
    for (k=0;k<cmem[c].size;k++) {
      l=mem[cmem[c].start+k].litno;
      fprintf(out_file," %s%.8s",
        l&1? "~": "", vmem[l>>1].name.ch8); /* $k$th literal */
    }
    fprintf(out_file,"\n");
  }
}

@*Doing it. Now comes ye olde basic backtrack.

Before we get started, however, we must prime the ready stack,
by discovering all of the forced moves, if any, that are present
in the given problem.

@<Initialize the ready stack@>=
@<Locate all the clauses of size 1@>;
@<Locate all the variables of constant sign@>;

@ @<Locate all the clauses of size 1@>=
for (c=clauses;c;c--) if (o,cmem[c].size==1) {
  o,p=cmem[c].start, l=mem[p].litno, k=l>>1;
  if (verbose&show_details)
    fprintf(stderr,"Clause %d forces %s%.8s\n",c,l&1?"~":"",vmem[k].name.ch8);
  if (o,mem[varcell(k)].ready_link) { /* variable |k| is ready already */
    if (mem[varcell(k)].litno!=l) goto backtrack; /* contradictory choices */
  }@+else {
    oo,p=mem[head].ready_link, mem[head].ready_link=varcell(k);
    o, mem[varcell(k)].ready_link=p, mem[varcell(k)].litno=l;
    o,p=mem[varcell(k)].flink, q=mem[varcell(k)].blink;
    oo,mem[p].blink=q, mem[q].flink=p;
    ready++;
  }
}

@ @<Locate all the variables of constant sign@>=
for (l=0;l<vars+vars;l++) if (o,mem[l].listsize==0) {
  k=l>>1;
  if ((l&1)==0 && (o,mem[l+1].listsize==0)) {
    if (verbose&show_details)
      fprintf(stderr,"(Variable %.8s isn't used)\n",vmem[k].name.ch8);
    /* this unusual case can result from a clause like \.{foo x1 ~x1} */
  }@+else {
    if (verbose&show_details)
      fprintf(stderr,"Can assume %s%.8s\n",l&1?"":"~",vmem[k].name.ch8);
    if (o,mem[varcell(k)].ready_link) { /* variable |k| is ready already */
      if (mem[varcell(k)].litno==l) goto backtrack; /* contradiction */
    }@+else {
      oo,p=mem[head].ready_link, mem[head].ready_link=varcell(k);
      o, mem[varcell(k)].ready_link=p, mem[varcell(k)].litno=l^1;
      o,p=mem[varcell(k)].flink, q=mem[varcell(k)].blink;
      oo,mem[p].blink=q, mem[q].flink=p;
      ready++;
    }
  }
}  

@ At level |l| of the backtrack process we record the variable whose value is
being specified, |smem[l].var|, and its chosen value, |smem[l].move|.
The latter value is 0 or 1 if the variable was on the to-do list and
we're trying first to make it true or false, respectively;
it is 3 or 2 if that move failed and we're trying the other alternative.
It is 4 or 5 if the variable was on the ready stack and set
respectively to true or false.

@<Solve the problem@>=
level=0;
@<Initialize the ready stack@>;
newlevel: /* |sanity();| */
if (ready) {
  oo,p=mem[head].ready_link,q=mem[p].ready_link,l=mem[p].litno;
  o,mem[head].ready_link=q; /* we leave |mem[p].ready_link| unchanged */
  o,smem[level].var=p, smem[level].move=4+(l&1);
  ready--;
}@+else {
  oo,p=mem[head].flink,q=mem[p].flink, l=(p-vars-vars)<<1;
  oo,mem[head].flink=q, mem[q].blink=head;
  ooo,smem[level].move=mem[l].listsize<mem[l+1].listsize;
  smem[level].var=p;
  l|=smem[level].move&1;
}
if (verbose&show_choices) {
  fprintf(stderr,"Level %d, trying %s%.8s",
    level,l&1?"~":"",vmem[l>>1].name.ch8);
  if (verbose&show_details) {
    if (smem[level].move>=4)
      fprintf(stderr," (%d, %d ready"@q)@>,mem[l].listsize, ready+1);
    else fprintf(stderr," (%d:%d",mem[l].listsize,mem[l^1].listsize);
    fprintf(stderr,", %d active, %lld mems)",active,mems);
  }
  fprintf(stderr,"\n");
}
if (delta && (mems>=thresh)) thresh+=delta,print_state(level);
if (active==mem[l].listsize) goto satisfied; /* success! */
o,smem[level].ready=ready;
tryit: @<Remove literal |l^1| from its clauses;
  |goto try_again| if a contradiction arises@>;
@<Inactivate all clauses that contain |l|;
  |goto try_again| if a contradiction arises@>;
level++;@+goto newlevel;
try_again: @<Adjust the ready stack to match |smem[level].ready|@>;
if (o,smem[level].move<2) {
  o,smem[level].move=3-smem[level].move;
  l=((smem[level].var-vars-vars)<<1)+(smem[level].move&1);
  if (verbose&show_choices) {
    fprintf(stderr,"Level %d, trying again",level);
    if (verbose&show_details)
      fprintf(stderr," (%d active, %lld mems)\n",active,mems);
    else fprintf(stderr,"\n");
  }
  goto tryit;
}
@<Restore the variable cell that changed at the beginning of this level@>;
backtrack:@+if (level) @<Backtrack to the previous level@>;
if (1) printf("~\n"); /* the formula was unsatisfiable */
else {
satisfied: @<Print the solution found@>;
}

@ We've sorted the clauses, but perhaps that was a mistake: Items on the
ready stack will change the order of decisions, so we might need to remove
a literal from the middle of its clause. That's awkward, with our
chosen data structure; it implies swapping the cell to the end of
its clause, and changing a whole bunch of links. I plan to measure
how often that happens; maybe the cells should be doubly linked
in two directions?

Another issue arises in this step too: We might create a clause
of length one that contradicts a previously seen clause of length one.
In that case we must undo the partial updates we've made;
and purists will shudder, because the best way to do that is
to jump into the middle of the main unremoving loop below.
(That loop will undo everything and lead to |try_again|, as desired.)

@<Remove literal |l^1|...@>=
for (o,k=mem[l^1].flink;k>=nonspec;k=kk) {
  o,kk=mem[k].flink;
  oo,c=mem[k].owner, i=cmem[c].size, p=cmem[c].start+i-1;
  if (k!=p) @<Swap cells |k| and |p|@>;
  if (i==2) {
    ll=mem[p-1].litno, j=ll>>1;
    if (verbose&show_details)
      fprintf(stderr,"Clause %d forces %s%.8s\n",
             c,ll&1?"~":"",vmem[j].name.ch8);
    if (o,mem[varcell(j)].ready_link) { /* variable |j| is ready already */
      if (mem[varcell(j)].litno!=ll) goto backup1; /* contradictory choices */
    }@+else {
      oo,p=mem[head].ready_link, mem[head].ready_link=varcell(j);
      o, mem[varcell(j)].ready_link=p, mem[varcell(j)].litno=ll;
      o,p=mem[varcell(j)].flink, q=mem[varcell(j)].blink;
      oo,mem[p].blink=q, mem[q].flink=p;
      ready++;
    }
  }
  o,cmem[c].size=i-1;
}

@ It's necessary to swap only some of the fields, because the lists for
variables already assigned need not be well formed. All we need in cell |p|
is to retain enough information to unswap if necessary. Cell |k| must,
however, be doubly linked into the list that formerly held cell |p|.

@<Swap cells |k| and |p|@>=
{
  o,pp=mem[p].flink,qq=mem[p].blink;
  o,mem[p].blink=mem[k].blink; /* we'll use this to come back */
  oo,mem[pp].blink=mem[qq].flink=k;
  o,mem[k].flink=pp,mem[k].blink=qq;
  oo,mem[k].litno=mem[p].litno;
}

@ Here's what we'll need to do when backtracking. The ready stack
will be restored after this loop has finished. Notice that we must
traverse the list backwards, because we might enter it at |backup1|.

@<Unremove literal |l^1| from its clauses@>=
for (o,kk=l^1,k=mem[kk].blink; k>=nonspec; ) {
  oo,c=mem[k].owner, i=cmem[c].size, p=cmem[c].start+i;  
  o,cmem[c].size=i+1;
backup1:@+if (k!=p) { /* must unswap cells |k| and |p| */
    o,pp=mem[k].flink,qq=mem[k].blink;
    oo,mem[pp].blink=mem[qq].flink=p;
    o,mem[k].litno=l^1; /* |mem[p].litno| hasn't changed */
    oo,mem[k].flink=kk, mem[k].blink=mem[p].blink;
    o,mem[p].blink=qq; /* |mem[p].flink| hasn't changed */
    kk=k, k=mem[k].blink;
  }@+else o,kk=k,k=mem[k].blink;
}

@ A subtle point arises here: Consider the clauses
$(x_1\vee x_2)\wedge(x_1\vee\bar x_2)\wedge(\bar x_1\vee x_3)$, which
are satisfied by $\{x_1,x_3\}$. If we choose $x_1$, we will see that
both $x_2$ and $\bar x_2$ can be assumed; but that is {\it not\/} a
contradiction! Indeed, when a variable is already on the ready list,
we should not check for contradictions in this step. A literal that
appears in a singleton clause won't have its |listsize| reach zero;
so a potential contradiction can arise here only when a variable has
dropped out of all the active clauses. In such cases we might as well leave
it on the ready list.

@<Inactivate all clauses that contain |l|...@>=
for (o,k=mem[l].flink;k>=nonspec;o,k=mem[k].flink) {
  o,c=mem[k].owner;
  for (o,j=cmem[c].size-1,p=cmem[c].start+j;(int)j>=0;p--,j--)
   if (o,mem[p].litno!=l) {
    o,ll=mem[p].litno, i=mem[ll].listsize-1;
    if (i==0) {
      kk=ll>>1;
      if (verbose&show_details)
        fprintf(stderr,"Can assume %s%.8s\n",ll&1?"":"~",vmem[kk].name.ch8);
      if (o,mem[varcell(kk)].ready_link==0) {
        oo,pp=mem[head].ready_link, mem[head].ready_link=varcell(kk);
        o, mem[varcell(kk)].ready_link=pp, mem[varcell(kk)].litno=ll^1;
        o,pp=mem[varcell(kk)].flink, qq=mem[varcell(kk)].blink;
        oo,mem[pp].blink=qq, mem[qq].flink=pp;
        ready++;
      }
    }
    o,q=mem[p].flink, r=mem[p].blink;
    oo,mem[q].blink=r, mem[r].flink=q;
    o,mem[ll].listsize=i;
  }
}
active-=mem[k].listsize;

@ And here again we must traverse the list
in the reverse direction from what we had before.
In fact, the lists inside the list must also be treated backwards.

@<Reactivate all clauses that contain |l|@>=
for (o,k=mem[l].blink;k>=nonspec;o,k=mem[k].blink) {
  o,c=mem[k].owner;
  for (o,p=cmem[c].start,j=0;j<cmem[c].size;p++,j++) if (o,mem[p].litno!=l) {
    o,q=mem[p].flink, r=mem[p].blink;
    oo,mem[q].blink=p, mem[r].flink=p;
    oo,mem[mem[p].litno].listsize++;
  }
}
o,active+=mem[k].listsize;

@ @<Backtrack to the previous level@>=
{
  level--;
  o,l=((smem[level].var-vars-vars)<<1)+(smem[level].move&1);
  @<Reactivate all clauses that contain |l|@>;
  @<Unremove literal |l^1|...@>;
  goto try_again;
}

@ @<Adjust the ready stack to match |smem[level].ready|@>=
for (o,j=smem[level].ready;ready>j;ready--) {
  ooo,k=mem[head].ready_link, mem[head].ready_link=mem[k].ready_link;
  o,mem[k].ready_link=0;
  o,p=mem[k].flink, q=mem[k].blink;
  oo,mem[p].blink=mem[q].flink=k;
}

@ @<Restore the variable cell that changed at the beginning of this level@>=
if (smem[level].move>=4) oo,mem[head].ready_link=smem[level].var,ready++;
else oo,oo,q=mem[head].flink,mem[head].flink=mem[q].blink=smem[level].var;

@ @<Print the solution found@>=
for (k=0;k<=level;k++) {
  l=((smem[k].var-vars-vars)<<1)+(smem[k].move&1);
  printf(" %s%.8s",l&1?"~":"",vmem[l>>1].name.ch8);
  if (out_file) fprintf(out_file," %s%.8s",l&1?"":"~",vmem[l>>1].name.ch8);
}
printf("\n");
if (level<vars-1) {
  if (verbose&show_unused_vars) printf("(Unused:");
  for (p=mem[head].ready_link;p!=ready_sentinel;p=mem[p].ready_link) {
    if (verbose&show_unused_vars) printf(" %.8s",vmem[p-vars-vars].name.ch8);
    if (out_file) fprintf(out_file," %.8s",vmem[p-vars-vars].name.ch8);
  }
  for (p=mem[head].flink;p!=head;p=mem[p].flink) {
    if (verbose&show_unused_vars) printf(" %.8s",vmem[p-vars-vars].name.ch8);
    if (out_file) fprintf(out_file," %.8s",vmem[p-vars-vars].name.ch8);
  }
  if (verbose&show_unused_vars) printf(")\n");
}
if (out_file) fprintf(out_file,"\n");

@*Index.
