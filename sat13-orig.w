\datethis
@s cell int
@s variable int
@s literal int
@s mod and
\let\Xmod=\bmod % this is CWEB magic for using "mod" instead of "%"

@*Intro. This program is part of a series of ``SAT-solvers'' that I'm putting
together for my own education as I prepare to write Section 7.2.2.2 of
{\sl The Art of Computer Programming}. My intent is to have a variety of
compatible programs on which I can run experiments to learn how different
approaches work in practice.

I'm hoping that this one, which has the lucky number {\mc SAT13},
will be the fastest of all, on a majority of the
example satisfiability problems that I've been exploring.
Why? Because it is based on the ``modern'' ideas of so-called
{\it conflict driven clause learning\/} (CDCL) solvers. This approach,
pioneered notably by Sakallah and Marques-Silva ({\mc GRASP}) and
by Moskewicz, Madigan, Zhao, Zhang, Malik ({\mc CHAFF}), has reportedly
revolutionized the field, making {\mc SAT}-solvers applicable to large-scale 
industrial problems.

My model for {\mc SAT13} has been E\'en and S\"orensson's MiniSAT solver,
together with the Biere's PicoSAT solver, both of which were at one
time representative of world-class CDCL implementations. The technology has
continued to improve, and to become more complex than appropriate for
my book to survey; therefore I have not added all the latest bells and whistles.
But I think this program decently represents the main CDCL paradigms.

{\sl Important Note:}\enspace The present program is essentially my
first draft, which used some experimental ideas that I have now
abandoned because they didn't work out as expected. I'm archiving
this code now, just in case some other researcher might be inspired
to develop a new approach that incorporates one or more of those
ideas, meanwhile correcting and enhancing them so that they really are helpful!
The code below is incomplete, because I stopped working on it before
including the logic for full runs or restarts, or for contracting the database
of learned clauses. The following paragraph, quoted from the first draft,
expresses my feelings at the time:

{\smallskip\narrower\it\noindent
While writing this I could not resist adding some ideas of my own about
``improving a reason.'' Some extra work is needed, and the algorithm
gets a bit more complicated; therefore I might jettison the approach later.
I've been encouraged to make this experiment because of the potential for
significant gains; and even if the new ideas don't pan out, I do know
that I've been learning a lot while writing this code.\looseness=-1
\par}

\smallskip
If you have already read {\mc SAT10} (or some other program of this
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
be `\.{\~x1} \.{\~x2} \.{x3}', in some order, possibly together
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
@d O "%" /* used for percent signs in format strings */
@d mod % /* used for percent signs denoting remainder in \CEE/ */

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
  register int h,hp,i,j,jj,k,kk,l,ll,lll,p,q,r,s;
  register int c,la,t,u,v,w,x,y;
  register double au,av;
  @<Process the command line@>;
  @<Initialize everything@>;
  @<Input the clauses@>;
  if (verbose&show_basics)
    @<Report the successful completion of the input phase@>;
  @<Set up the main data structures@>;
  imems=mems, mems=0;
  @<Solve the problem@>;
  @<Print farewell messages@>;
}

@ On the command line one can specify any or all of the following options:
\smallskip
\item{$\bullet$}
`\.v$\langle\,$integer$\,\rangle$' to enable various levels of verbose
 output on |stderr|.
\item{$\bullet$}
`\.c$\langle\,$positive integer$\,\rangle$' to limit the levels on which
clauses are shown.
\item{$\bullet$}
`\.h$\langle\,$positive integer$\,\rangle$' to adjust the hash table size.
\item{$\bullet$}
`\.b$\langle\,$positive integer$\,\rangle$' to adjust the size of the input
buffer.
\item{$\bullet$}
`\.s$\langle\,$integer$\,\rangle$' to define the seed for any random numbers
that are used.
\item{$\bullet$}
`\.d$\langle\,$integer$\,\rangle$' to set |delta| for periodic state reports.
(See |print_state|.)
\item{$\bullet$}
`\.m$\langle\,$positive integer$\,\rangle$' to adjust the maximum memory size.
(The binary logarithm is specified; it must be at most 31.)
\item{$\bullet$}
`\.w$\langle\,$integer$\,\rangle$' to set |warmups|, the number of ``full runs''
done after a restart.
\item{$\bullet$}
`\.i$\langle\,$integer$\,\rangle$' to set |improvesize|, the maximum size of
clauses examined for potentially improving a reason.
\item{$\bullet$}
`\.S$\langle\,$integer$\,\rangle$' to adjust |slide|, the parameter that limits
the levels of sliding permitted in the trail.
\item{$\bullet$}
`\.r$\langle\,$positive float$\,\rangle$' to adjust |var_rho|, the
damping factor for variable activity scores.
\item{$\bullet$}
`\.R$\langle\,$positive float$\,\rangle$' to adjust |clause_rho|, the
damping factor for clause activity scores.
\item{$\bullet$}
`\.p$\langle\,$positive float$\,\rangle$' to adjust |rand_prob|, the
probability that a branch variable is chosen randomly.
\item{$\bullet$}
`\.x$\langle\,$filename$\,\rangle$' to output a
solution-eliminating clause to the specified file. If the given problem is
satisfiable in more than one way, a different solution can be obtained by
appending that file to the input.
\item{$\bullet$}
`\.l$\langle\,$filename$\,\rangle$' to output some learned clauses
to the specified file, for purposes of restarting.
\item{$\bullet$}
`\.L$\langle\,$filename$\,\rangle$' to output all of the learned clauses
to the specified file. (This data can be used, for example, as a certificate
of unsatisfiability.)

@<Process the command line@>=
for (j=argc-1,k=0;j;j--) switch (argv[j][0]) {
@<Respond to a command-line option, setting |k| nonzero on error@>;
default: k=1; /* unrecognized command-line option */
}
@<If there's a problem, print a message about \.{Usage:} and |exit|@>;

@ @d show_basics 1 /* |verbose| code for basic stats */
@d show_choices 2 /* |verbose| code for backtrack logging */
@d show_details 4 /* |verbose| code for further commentary */
@d show_gory_details 8 /* |verbose| code for more yet */
@d show_watches 16 /* |verbose| code to show when a watch list changes */

@<Glob...@>=
int random_seed=0; /* seed for the random words of |gb_rand| */
int verbose=show_basics; /* level of verbosity */
uint show_choices_max=1000000; /* above this level, |show_choices| is ignored */
int hbits=8; /* logarithm of the number of the hash lists */
int buf_size=1024; /* must exceed the length of the longest input line */
FILE *out_file; /* file for optional output of a solution-avoiding clause */
char *out_name; /* its name */
FILE *restart_file; /* file for learned clauses to be used in a restart */
char *restart_name; /* its name */
FILE *learned_file; /* file for output of every learned clause */
char *learned_name; /* its name */
ullng imems,mems; /* mem counts */
ullng bytes; /* memory used by main data structures */
ullng nodes; /* the number of nodes entered */
ullng thresh=0; /* report when |mems| exceeds this, if |delta!=0| */
ullng delta=0; /* report every |delta| or so mems */
uint memk_max=memk_max_default; /* binary log of the maximum size of |mem| */
uint max_cells_used; /* how much of |mem| has ever held data? */
float var_rho=0.95; /* damping factor for variable activity */
float clause_rho=0.999; /* damping factor for clause activity */
float rand_prob=0.02; /* probability of choosing at random */
uint rand_prob_thresh; /* $2^{31}$ times |rand_prob| */
int warmups=0; /* the number of full runs done after restart */
int improvesize=4; /* upper bound on clause size in the improvement heuristic */
int slide=4; /* maximum amount of sliding in the trail */
ullng total_learned; /* we've learned this many clauses */
double cells_learned; /* and this is their total length */
double cells_prelearned; /* which was this before simplification */
ullng discards; /* we quickly discarded this many of those clauses */
ullng trivials; /* we learned this many intentionally trivial clauses */

@ @<Respond to a command-line option, setting |k| nonzero on error@>=
case 'v': k|=(sscanf(argv[j]+1,""O"d",&verbose)-1);@+break;
case 'c': k|=(sscanf(argv[j]+1,""O"d",&show_choices_max)-1);@+break;
case 'h': k|=(sscanf(argv[j]+1,""O"d",&hbits)-1);@+break;
case 'b': k|=(sscanf(argv[j]+1,""O"d",&buf_size)-1);@+break;
case 's': k|=(sscanf(argv[j]+1,""O"d",&random_seed)-1);@+break;
case 'd': k|=(sscanf(argv[j]+1,""O"lld",&delta)-1);@+thresh=delta;@+break;
case 'm': k|=(sscanf(argv[j]+1,""O"d",&memk_max)-1);@+break;
case 'w': k|=(sscanf(argv[j]+1,""O"d",&warmups)-1);@+break;
case 'i': k|=(sscanf(argv[j]+1,""O"d",&improvesize)-1);@+break;
case 'S': k|=(sscanf(argv[j]+1,""O"d",&slide)-1);@+break;
case 'r': k|=(sscanf(argv[j]+1,""O"f",&var_rho)-1);@+break;
case 'R': k|=(sscanf(argv[j]+1,""O"f",&clause_rho)-1);@+break;
case 'p': k|=(sscanf(argv[j]+1,""O"f",&rand_prob)-1);@+break;
case 'x': out_name=argv[j]+1, out_file=fopen(out_name,"w");
  if (!out_file)
    fprintf(stderr,"Sorry, I can't open file `"O"s' for writing!\n",out_name);
  break;
case 'l': restart_name=argv[j]+1, restart_file=fopen(restart_name,"w");
  if (!restart_file)
    fprintf(stderr,"Sorry, I can't open file `"O"s' for writing!\n",
      restart_name);
  break;
case 'L': learned_name=argv[j]+1, learned_file=fopen(learned_name,"w");
  if (!learned_file)
    fprintf(stderr,"Sorry, I can't open file `"O"s' for writing!\n",
      learned_name);
  break;

@ @<If there's a problem, print...@>=
if (k || hbits<0 || hbits>30 || buf_size<=0 || memk_max<2 || memk_max>31 ||
       rand_prob<0.0 || var_rho<=0.0 || clause_rho<=0.0) {
  fprintf(stderr,
     "Usage: "O"s [v<n>] [c<n>] [h<n>] [b<n>] [s<n>] [d<n>] [m<n>]",argv[0]);
  fprintf(stderr," [w<n>] [i<n>] [S<n>] [r<f>] [R<f>] [p<f>]");
  fprintf(stderr," [x<foo>] [l<bar>] [L<baz>] < foo.dat\n");
  exit(-1);
}

@ @<Print farewell messages@>=
if (verbose&show_basics) {
  fprintf(stderr,
    "Altogether "O"llu+"O"llu mems, "O"llu bytes, "O"llu node"O"s,",
                   imems,mems,bytes,nodes,nodes==1?"":"s");
  fprintf(stderr," "O"llu clauses learned",total_learned);
  if (total_learned)
    fprintf(stderr," (ave "O".1f->"O".1f)",
      cells_prelearned/(double)total_learned,
      cells_learned/(double)total_learned);
  fprintf(stderr,", "O"u memcells.\n",max_cells_used);
  if (learned_file)
    fprintf(stderr,"Learned clauses written to file `"O"s'.\n",learned_name);
  if (trivials)
    fprintf(stderr,"("O"lld learned clause"O"s were trivial.)\n",
                  trivials,trivials==1?"":"s");
  if (discards)
    fprintf(stderr,"("O"lld learned clause"O"s were discarded.)\n",
                  discards,discards==1?"":"s");
}


@*The I/O wrapper. The following routines read the input and absorb it into
temporary data areas from which all of the ``real'' data structures
can readily be initialized. My intent is to incorporate these routines into all
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
  ullng lng;
} octa;
typedef struct tmp_var_struct {
  octa name; /* the name (one to eight ASCII characters) */
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
int unaries; /* how many were unary? */
int binaries; /* how many were binary? */
ullng cells; /* how many occurrences of literals in clauses? */

@ @<Initialize everything@>=
gb_init_rand(random_seed);
buf=(char*)malloc(buf_size*sizeof(char));
if (!buf) {
  fprintf(stderr,"Couldn't allocate the input buffer (buf_size="O"d)!\n",
            buf_size);
  exit(-2);
}
hash=(tmp_var**)malloc(sizeof(tmp_var)<<hbits);
if (!hash) {
  fprintf(stderr,"Couldn't allocate "O"d hash list heads (hbits="O"d)!\n",
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
      "The clause on line "O"lld ("O".20s...) is too long for me;\n",clauses,buf);
    fprintf(stderr," my buf_size is only "O"d!\n",buf_size);
    fprintf(stderr,"Please use the command-line option b<newsize>.\n");
    exit(-4);
  }
  @<Input the clause in |buf|@>;
}
if ((vars>>hbits)>=10) {
  fprintf(stderr,"There are "O"lld variables but only "O"d hash tables;\n",
     vars,1<<hbits);
  while ((vars>>hbits)>=10) hbits++;
  fprintf(stderr," maybe you should use command-line option h"O"d?\n",hbits);
}
clauses-=nullclauses;
if (clauses==0) {
  fprintf(stderr,"No clauses were input!\n");
  exit(-77);
}
if (vars>=0x80000000) {
  fprintf(stderr,"Whoa, the input had "O"llu variables!\n",cells);
  exit(-664);
}
if (clauses>=0x80000000) {
  fprintf(stderr,"Whoa, the input had "O"llu clauses!\n",cells);
  exit(-665);
}
if (cells>=0x100000000) {
  fprintf(stderr,"Whoa, the input had "O"llu occurrences of literals!\n",cells);
  exit(-666);
}

@ @<Input the clause in |buf|@>=
for (j=k=0;;) {
  while (buf[j]==' ') j++; /* scan to nonblank */
  if (buf[j]=='\n') break;
  if (buf[j]<' ' || buf[j]>'~') {
    fprintf(stderr,"Illegal character (code #"O"x) in the clause on line "O"lld!\n",
      buf[j],clauses);
    exit(-5);
  }
  if (buf[j]=='~') i=1,j++;
  else i=0;
  @<Scan and record a variable; negate it if |i==1|@>;
}
if (k==0) {
  fprintf(stderr,"(Empty line "O"lld is being ignored)\n",clauses);
  nullclauses++; /* strictly speaking it would be unsatisfiable */
}
goto clause_done;
empty_clause: @<Remove all variables of the current clause@>;
clause_done: cells+=k;
if (k==1) unaries++;
else if (k==2) binaries++;

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
        "Variable name "O".9s... in the clause on line "O"lld is too long!\n",
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
  p->stamp=0;
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
  fprintf(stderr,"(The clause on line "O"lld is always satisfied)\n",clauses);
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
fprintf(stderr,
  "("O"lld variables, "O"lld clauses, "O"llu literals successfully read)\n",
                       vars,clauses,cells);

@*SAT solving, version 13. 
The methods used in this program have much in common with what we've
seen before in {\mc SAT0}, {\mc SAT1}, etc.; yet conflict-driven
clause learning is somewhat different. So we might as well derive everything
from first principles.

As usual, our goal is to find strictly distinct literals that satisfy
all of the given clauses, or to prove that those clauses can't all be
satisfied. Thus our subgoal, after having created a ``trail'' $l_0l_1\ldots l_t$
of literals that don't falsify any clause, will be to extend that sequence
until finding a solution, and without failing unless no
solution exists.

If there's a clause $c$ of the form $l\lor\bar a_1\lor\cdots\lor\bar a_k$,
where $a_1$ through~$a_k$ are in the trail but $l$ isn't, we append~$l$
to the trail and say that $c$ is its ``reason.'' This operation, often
called unit propagation, is basic to our program; we shall simply call
it {\it forcing}. (We're forced to make $l$ true, if $a_1$ through $a_k$
are true, because $c$ must be satisfied.) A {\it conflict\/} occurs
if the complementary literal $\bar l$ is already in the trail,
because $l$ can't be both true and false;
but let's assume for now that no conflicts arise.

If no such forcing clause exists, and if the clauses aren't all satisfied,
we choose a new distinct literal in some heuristic way, and append it to
the trail with a ``reason'' of~0. Such literals are called {\it decisions}.
They partition the trail into a sequence of decision levels, with
literal $l_j$ belonging to level~$d$ if and only if $i_d\le j< i_{d+1}$.
In general $0\le i_1<i_2<\cdots{}$; and we also define $i_0=0$.
(Level~0 is special; it contains literals that are forced by clauses of
length~1, if such clauses exist. Any such literals are unconditionally true.
Every other level begins with exactly one decision.)

\def\sucp{\mathrel{{\succ}\!^+}}
If the reason for $l$ includes the literal $\bar l'$, we say
``$l$ depends directly on~$l'$,'' and we write $l\succ l'$.
And if there's a chain of one or more direct dependencies
$l\succ l_1\succ\cdots\succ l_k=l'$, we write $l\sucp l'$ and
say simply that ``$l$ depends on~$l'$.'' For example, given the
three clauses $a$ and $\bar a\lor b$ and $\bar b\lor\bar c\lor d$,
we might begin the trail with $l_0l_1l_2l_3=abcd$, where the first clause
is the reason for~$a$, the second clause is the reason for~$b$, and the
third clause is the reason for~$d$, while $c$ is a decision.
Then $d\succ c$ and $d\succ b$ and $b\succ a$; hence $d\sucp a$.

Notice that we cannot have $l\sucp l$; the dependency relation is a partial
ordering. Furthermore,
every literal $l$ that's forced at level $d>0$ depends directly on some
{\it other\/} literal on that same level; hence $l$ must necessarily
depend on the $d\,$th decision.

The reason for reasons is that we need to deal with conflicts. We will see
that every conflict allows us to construct a new clause~$c$ that must be
true whenever the existing clauses are satisfiable, although $c$ itself
does not contain any existing clause. Therefore we can ``learn''~$c$ by
adding it to the existing clauses, and we can try again. This learning
process can't go on forever, because only finitely many clauses are possible.
Sooner or later we will therefore either find a solution or learn the
empty clause.

A conflict clause $c_d$ on decision level~$d$ has the form
$\bar l\lor\bar a_1\lor\cdots\lor\bar a_k$, where $l$ and all the $a$'s
belong to the trail; furthermore $l$ and at least one $a_i$ belong to
level~$d$. We can assume that $l$ is maximal, with respect to the
dependency ordering, of all the literals in $c_d$ on level~$d$.
Hence $l$ cannot be the $d\,$th decision; and it has a
reason, say $l\lor\bar a'_1\lor\cdots\lor\bar a'_{k'}$. Resolving $c_d$
with this reason gives the clause $c=\bar a_1\lor\cdots\lor\bar a_k\lor\bar
a'_1\lor\cdots\lor\bar a'_{k'}$, which includes at least one literal~$\bar l'$
for which $l'$ is on level~$d$. If more than one such literal is present,
we can resolve $c$ with the reason of a maximal~$l'$ (with respect to
the dependency ordering); the result will involve negations of literals that
are lower in the ordering. By repeating this process we'll eventually obtain
$c$ of the form $\bar l'\lor\bar b_1\lor\cdots\lor\bar b_r$, where
$l'$ is on level~$d$ and $b_1$ through~$b_r$ are on lower levels.

Such a $c$ is learnable, as desired, because it can't contain any
existing clause. (Every subclause, including $c$ itself,
would have given us something to
force at a lower level.) We can now discard levels $>d'$ of the trail, where
$d'$ is the maximum level of $b_1$ through $b_r$; and we append
$\bar l'$ to the end of level~$d'$, with $c$ as its reason.
The forcing process now resumes at level~$d'$, as if the learned
clause had been present all along.

Okay, that's the basic idea of conflict-driven clause learning.
Many other issues will come up as we refine it, of course. For example,
we'll see that the clause $c$ can often be simplified by removing
one or more of its literals~$\bar b_i$. And we'll want to ``unlearn'' clauses
that outlive their usefulness.

@ What data structures support this procedure? We obviously need to
represent the trail, as well as the levels, values, and reasons for
each of its literals.

A principal concern is to make forcing as fast as possible. Many
applications involve numerous binary clauses (that is, clauses of length~2);
and binary clauses make forcing quite easy. So we should have a
special mechanism to derive binary implications quickly.

Long clauses are also important. (Even if they aren't common in the input,
the clauses that we learn often turn out to involve dozens of literals.)
``Watch lists'' provide a good way to recognize when such clauses
become ready for forcing: We choose two literals in each long clause,
neither of which is false, and we pay no attention to that clause until one of
its watched literals becomes false. In the latter case, we'll be able to
watch it with another literal, unless the clause has become true or it's ready
to force something. (We've used a similar idea, but with only one watched
literal per clause, in {\mc SAT0W} and {\mc SAT10}.)

We'll want a good heuristic for choosing the decision literals.
This program adopts the strategy of E\'en and S\"orensson's
MiniSAT, which associates a floating-point {\it activity\/}
score with each variable, and uses a heap to choose the most
active variable.

Learned clauses also have somewhat analogous activity scores of their own,
as well as another measure of clause quality devised by Gilles Audemard
and Laurent Simon. The original clauses are static and stay in place,
but we must periodically decide which of the learned clauses to keep.

@<Glob...@>=
cell *mem; /* master array of clause data */
uint memsize; /* the number of cells allocated for it */
uint min_learned; /* boundary between original and learned clauses */
uint first_learned; /* address of the first learned clause */
uint max_learned; /* the first unused position of |mem| */
int max_lit; /* value of the largest legal literal */
uint *bmem; /* binary clause data */
literal *lmem; /* attributes of literals */
variable *vmem; /* attributes of variables */
uint *heap; /* priority queue for sorting variables by their activity */
int hn; /* number of items currently in the heap */
uint *trail; /* literals currently assumed, or forced by those assumptions */
int eptr; /* just past the end of the trail */
int ebptr; /* just past where binary propagations haven't been done yet */
int lptr; /* just past where we've checked nonbinary propagations */
int lbptr; /* just past where we've checked binary propagations */
uint *history; /* type of assertion, for diagnostic printouts */
int llevel; /* twice the current level */
int *leveldat; /* where levels begin; also conflict data on full runs */

@ Binary clauses $u\lor v$ are represented by putting $v$ into a list
associated with $\bar u$ and $u$ into a list associated with $\bar v$.
These ``binary implication'' lists are created once and for all at the
beginning of the run, as explained below.

Longer clauses (and binary clauses that are learned later) are
represented in a big array |mem| of 32-bit cells. The literals
of clause~|c| are |mem[c].lit|, |mem[c+1].lit|, |mem[c+2].lit|, etc.;
the first two of these are being ``watched.'' The number of literals,
|size(c)|, is |mem[c-1].lit|; and we keep links to other clauses
watching the same literals in |link0(c)=mem[c-2].lit| and
|link1(c)=mem[c-3].lit|.

(Incidentally, this linked structure for watch lists was originally introduced
in PicoSAT by Armin Biere [{\sl Journal on Satisfiability, Boolean Modeling
and Computation\/ \bf4} (2008), 75--97]. Nowadays the fastest solvers
use a more complicated mechanism called ``blocking literals,'' due to Niklas
S\"orensson, which is faster because it is more cache friendly. However,
I'm sticking to linked lists, because (1)~they don't need dynamic storage
allocation of sequential arrays; (2)~they use fewer memory accesses; and
(3)~on modern multithread machines they can be implemented so as to avoid the
cache misses, by starting up threads whose sole purpose is to preload the
link-containing cells into the cache. I~expect that software to facilitate
such transformations will be widely available before long.)

If |c| is the current reason for literal |l|, its first literal
|mem[c].lit| is always equal to |l|. This condition makes it easy
to tell if a given clause plays an important role in the current trail.

A learned clause is identifiable by the condition |c>=min_learned|.
Such clauses have additional information, which we use to decide whether
or not to keep them after memory has begun to fill up. For example,
|clause_act(c)=mem[c-4].flt| is the clause's activity score.

@d size(c) mem[(c)-1].lit
@d link0(c) mem[(c)-2].lit
@d link1(c) mem[(c)-3].lit
@d clause_extra 3 /* every clause has a 3-cell preamble */
@d clause_act(c) mem[(c)-4].flt
@d levels(c) mem[(c)-5].lit
@d learned_extra 2
   /* learned clauses have this many more cells in their preamble */

@<Type...@>=
typedef union {
  uint lit;
  float flt;
} cell;

@ The variables are numbered from 1 to |n|. The literals corresponding
to variable~|k| are |k+k| and |k+k+1|, standing respectively for $v$
and $\bar v$ if the $k$th variable is~$v$.

Several different kinds of data are maintained for each variable:
Its eight-character |name|; its |activity| score (used to indicate
relative desirability for being chosen to make the next decision);
its current |value|, which also encodes the level at which
the value was set; its current location, |tloc|, in the trail;
and its current location, |hloc|, in the heap
(which is used to find a maximum activity score). There's also |plevel|,
|oldval|, and |stamp|, which will be explained later.

@d bar(l) ((l)^1)
@d thevar(l) ((l)>>1)
@d litname(l) (l)&1?"~":"",vmem[thevar(l)].name.ch8 /* used in printouts */
@d poslit(v) ((v)<<1)
@d neglit(v) (((v)<<1)+1)
@d unset 0xffffffff /* value when the variable hasn't been assigned */
@d isknown(l) (vmem[thevar(l)].value!=unset)
@d iscontrary(l) ((vmem[thevar(l)].value^(l))&1)

@<Type...@>=
typedef struct {
  octa name;
  double activity;
  uint value;
  uint plevel;
  uint tloc;
  uint stamp;
  int hloc; /* is |-1| if the variable isn't in the heap */
  uint oldval;
} variable;

@ Special data for each literal goes into |lmem|, containing the literal's
|reason| for being true, the first clause (if any) that it watches,
and the boundaries of its binary implications in |bmem|.

@<Type...@>=
typedef struct {
  int reason; /* is negative for binary reasons, otherwise clause number */
  uint watch; /* head of the list of clauses watched by this literal */
  uint bimp_start; /* where binary implications begin in |bmem| */
  uint bimp_end; /* just after where they end (or zero if there aren't any) */
} literal;

@ Here is a subroutine that prints the binary implicant data for
a given literal. (Used only when debugging.)

@<Sub...@>=
void print_bimp(int l) {
  register uint la;
  printf(""O"s"O".8s("O"d) ->",litname(l),l);
  if (lmem[l].bimp_end) {
    for (la=lmem[l].bimp_start;la<lmem[l].bimp_end;la++)
      printf(" "O"s"O".8s("O"d)",litname(bmem[la]),bmem[la]);
  }
  printf("\n");
}

@ Similarly, we can print the numbers of all clauses that |l| is currently
watching.

@<Sub...@>=
void print_watches_for(int l) {
  register uint c;
  printf(""O"s"O".8s("O"d) watches",litname(l),l);
  for (c=lmem[l].watch;c;) {
    printf(" "O"u",c);
    if (mem[c].lit==l) c=link0(c);
    else c=link1(c);
  }
  printf("\n");
}  

@ And we also sometimes need to see the literals of a given clause.

@<Sub...@>=
void print_clause(uint c) {
  register int k;
  printf(""O"u:",c);
  for (k=0;k<size(c);k++)
    printf(" "O"s"O".8s("O"u)",litname(mem[c+k].lit),mem[c+k].lit);
  if (c<min_learned) printf("\n");
  else printf(" ("O".4e,"O"d)\n",clause_act(c),levels(c));
}

@ Speaking of debugging, here's a routine to check if the redundant
parts of our data structure have gone awry.

@d sanity_checking 1 /* set this to 0 to avoid sanity checks */

@<Sub...@>=
void sanity(int eptr) {
  register uint k,l,c,u,v,clauses,watches,vals,llevel;
  @<Check all clauses for spurious data@>;
  @<Check the watch lists@>;  
  @<Check the sanity of the heap@>;
  @<Check the trail@>;
  @<Check the variables@>;
}

@ @<Check all clauses for spurious data@>=
for (clauses=k=0,c=clause_extra;c<min_learned;k=c,c+=size(c)+clause_extra) {
  clauses++;
  if (link0(c)>=max_learned) {
    fprintf(stderr,"bad link0("O"u)!\n",c);
    return;
  }
  if (link1(c)>=max_learned) {
    fprintf(stderr,"bad link1("O"u)!\n",c);
    return;
  }
  if (size(c)<3)
    fprintf(stderr,"size("O"u)="O"d!\n",c,size(c));
  for (k=0;k<size(c);k++)
    if (mem[c+k].lit<2 || mem[c+k].lit>max_lit)
      fprintf(stderr,"bad lit "O"d of "O"d!\n",k,c);
}
if (c!=min_learned)
  fprintf(stderr,"bad last unlearned clause ("O"d)!\n",k);
else {
  for (k=0,c+=learned_extra;c<max_learned;
         k=c,c+=size(c)+clause_extra+learned_extra) {
    clauses++;
    if (link0(c)>=max_learned) {
      fprintf(stderr,"bad link0("O"u)!\n",c);
      return;
    }
    if (link1(c)>=max_learned) {
      fprintf(stderr,"bad link1("O"u)!\n",c);
      return;
    }
    if (size(c)<2)
      fprintf(stderr,"size("O"u)="O"d!\n",c,size(c));
    for (k=0;k<size(c);k++)
      if (mem[c+k].lit<2 || mem[c+k].lit>max_lit)
        fprintf(stderr,"bad lit "O"d of "O"d!\n",k,c);
  }
  if (c!=max_learned)
    fprintf(stderr,"bad last learned clause ("O"d)!\n",k);
}    

@ In bad cases this routine will get into a loop. I try to avoid
segmentation faults, but not loops.

@<Check the watch lists@>=
for (watches=0,l=2;l<=max_lit;l++) {
  for (c=lmem[l].watch;c;) {
    watches++;
    if (c>=max_learned) {
      fprintf(stderr,"clause "O"u in watch list "O"u out of range!\n",c,l);
      return;
    }
    if (mem[c].lit==l) c=link0(c);
    else if (mem[c+1].lit==l) c=link1(c);
    else {
      fprintf(stderr,"clause "O"u improperly on watch list "O"u!\n",c,l);
      return;
    }
  }
}
if (watches!=clauses+clauses)
  fprintf(stderr,""O"u clauses but "O"u watches!\n",clauses,watches);

@ @<Check the trail@>=
for (k=llevel=0;k<eptr;k++) {
  l=trail[k];
  if (l<2 || l>max_lit) {
    fprintf(stderr,"bad lit "O"u in trail["O"u]!\n",l,k);
    return;
  }
  if (vmem[thevar(l)].tloc!=k)
    fprintf(stderr,""O"s"O".8s has bad tloc ("O"d not "O"d)!\n",
           litname(l),vmem[thevar(l)].tloc,k);
  if (k==leveldat[llevel+2]) {
    llevel+=2;
    if (lmem[l].reason)
      fprintf(stderr,""O"s"O".8s("O"u), level "O"u, shouldn't have reason!\n",
                     litname(l),l,llevel>>1);
    if (vmem[thevar(l)].plevel)
      fprintf(stderr,""O"s"O".8s("O"u), level "O"u, shouldn't have plevel!\n",
                     litname(l),l,llevel>>1);
  }@+else {
    if (llevel && !lmem[l].reason)
      fprintf(stderr,""O"s"O".8s("O"u), level "O"u, should have reason!\n",
                     litname(l),l,llevel>>1);
    if (llevel && vmem[thevar(l)].plevel>=llevel)
      fprintf(stderr,""O"s"O".8s("O"u), level "O"u, has plevel "O"u!\n",
                     litname(l),l,llevel>>1,vmem[thevar(l)].plevel>>1);
  }
  if (lmem[bar(l)].reason)
    fprintf(stderr,""O"s"O".8s("O"u), level "O"u, comp has reason!\n",
                     litname(l),l,llevel>>1);
  if (vmem[thevar(l)].value!=llevel+(l&1))
    fprintf(stderr,""O"s"O".8s("O"u), level "O"u, has bad value!\n",
                     litname(l),l,llevel>>1);
  if (lmem[l].reason<=0) {
    if (lmem[l].reason==-1 || lmem[l].reason<-max_lit)
      fprintf(stderr,
         ""O"s"O".8s("O"u), level "O"u, has wrong binary reason ("O"u)!\n",
                  litname(l),l,llevel>>1,c);
  }@+else {    
    c=lmem[l].reason;
    if (mem[c].lit!=l)
      fprintf(stderr,""O"s"O".8s("O"u), level "O"u, has wrong reason ("O"u)!\n",
                    litname(l),l,llevel>>1,c);
    u=bar(mem[c+1].lit);
    if (vmem[thevar(u)].value!=llevel+(u&1))
      fprintf(stderr,""O"s"O".8s("O"u), level "O"u, has bad reason ("O"u)!\n",
                    litname(l),l,llevel>>1,c);
  }
}

@ @<Check the variables@>=
for (vals=0,v=1;v<=vars;v++) {
  if (vmem[v].value>llevel+1) {
    if (vmem[v].value!=unset)
      fprintf(stderr,"strange val "O".8s (level "O"u)!\n",
           vmem[v].name.ch8,vmem[v].value>>1);
    else if (vmem[v].hloc<0)
      fprintf(stderr,""O".8s should be in the heap!\n",vmem[v].name.ch8);
  }@+else vals++;
}
if (vals!=eptr)
  fprintf(stderr,"I found "O"u values, but eptr="O"u!\n",vals,eptr);
  
@ In long runs it's helpful to know how far we've gotten. A numeric code
summarizes the histories of literals that appear in the current trail:
0 or 1 means that we're trying to set a variable
true or false, as a decision at the beginning of a level;
2 or 3 is similar, but after we've learned that the decision was wrong (hence
we've learned a clause that has forced the opposite decision);
4 or 5 is similar, but when the value was forced by
the decision at the previous decision node;
6 or 7 is similar, but after we learned that a previous decision
forces this one. (In the latter case, the learned clause forced a
variable that was not the decision variable at its level.)

Vertical lines are inserted before decisions that have been slid down.
For example, ``\.{615{\char'174}{\char'174}03}'' indicates that a former
non-decision literal has been learned to be true at level~0; also, a false
literal has been asserted at level 1, and that literal has forced another
to be true. Level~2 has been restarted twice by the sliding operation.
That level now begins by asserting a true literal;
then comes a false literal, whose truth had been asserted at level~3 (but that
assertion had led to a contradiction). 

A special |history| array is used to provide these base codes (0, 2, 4, or 6).
No mems are assessed for maintaining |history|, because it isn't used
in any decisions taken by the algorithm; it's purely for diagnostic purposes.

Entries in |history| are 32-bit unsigned integers consisting of the base code,
shifted left 28, plus the number of vertical lines that should appear
before it. At present the latter is zero except for code~0.
(I suppose that, in principle, I could maintain more of the history of
the ``learned'' literals of codes 2 and~6.)

@<Sub...@>=
void print_state(int eptr) {
  register uint j,k;
  fprintf(stderr," after "O"lld mems:",mems);
  for (k=0;k<eptr;k++) {
    j=history[k];
    if (j<2<<28)
      for (;j;j--) fprintf(stderr,"|");    
    fprintf(stderr,""O"d",(j>>28)+(trail[k]&1));
  }
  fprintf(stderr,"\n");
  fflush(stderr);
}

@ We might also like to see the complete trail, including names and reasons.

@<Sub...@>=
void print_trail(int eptr) {
  register int k;
  for (k=0;k<eptr;k++) {
    if (k>=vars || trail[k]<2 || trail[k]>max_lit) return;
    fprintf(stderr,""O"d: "O"d "O"d "O"s"O".8s("O"d)",
          k,(history[k]>>28)+(trail[k]&1),vmem[thevar(trail[k])].value>>1,
          litname(trail[k]),trail[k]);
    if (lmem[trail[k]].reason>0)
      fprintf(stderr," #"O"u\n",lmem[trail[k]].reason);
    else if (lmem[trail[k]].reason<0)
      fprintf(stderr," <- "O"s"O".8s\n",litname(-lmem[trail[k]].reason));
    else if (history[k]) fprintf(stderr," (slid "O"d)\n",history[k]);
    else fprintf(stderr,"\n");
  }
}

@*Initializing the real data structures.
We're ready now to convert the temporary chunks of data into the
form we want, and to recycle those chunks. The code below is, of course,
similar to what has worked in previous programs of this series.

@<Set up the main data structures@>=
@<Allocate the main arrays@>;
@<Copy all the temporary cells to the |mem| and |bmem| and |trail| arrays
   in proper format@>;
@<Copy all the temporary variable nodes to the |vmem| array in proper format@>;
@<Check consistency@>;
@<Allocate the auxiliary arrays@>;
@<Initialize the heap@>;

@ @<Allocate the main arrays@>=
free(buf);@+free(hash); /* a tiny gesture to make a little room */
@<Figure out how big |mem| ought to be@>;
mem=(cell*)malloc(memsize*sizeof(cell));
if (!mem) {
  fprintf(stderr,"Oops, I can't allocate the big mem array!\n");
  exit(-10);
}
bytes=max_cells_used*sizeof(cell);
vmem=(variable*)malloc((vars+1)*sizeof(variable));
if (!vmem) {
  fprintf(stderr,"Oops, I can't allocate the vmem array!\n");
  exit(-12);
}
bytes+=(vars+1)*sizeof(variable);
for (k=1;k<=vars;k++) o,vmem[k].value=unset,vmem[k].plevel=0;
max_lit=vars+vars+1;
lmem=(literal*)malloc((max_lit+1)*sizeof(literal));
if (!lmem) {
  fprintf(stderr,"Oops, I can't allocate the lmem array!\n");
  exit(-13);
}
bytes+=(max_lit+1)*sizeof(literal);
trail=(uint*)malloc(vars*sizeof(uint));
if (!trail) {
  fprintf(stderr,"Oops, I can't allocate the trail array!\n");
  exit(-14);
}
bytes+=vars*sizeof(uint);

@ The |mem| array will contain $2^k-1<2^{32}$ cells of four bytes each,
where $k$ is the parameter |memk_max|; this parameter is
|memk_max_default| (currently~22) by default, and changeable by the user
via \.m on the command line. (Apology: This program is for my own use in
experiments, so I haven't bothered to give it a more user-friendly interface.)

It will begin with data for all clauses of length 3 or more;
then come the learned clauses, which have slightly longer preambles.
During the initialization, some of the eventual space for learned
clauses is used temporarily to hold the binary clause information.

We will record in |bytes| and |max_cells_used| only the number of cells actually
utilized; this at least gives the user some clue about how big \.m should be.

@d memk_max_default 26 /* allow 64 million cells in |mem| by default */

@<Figure out how big |mem| ought to be@>=
{
  ullng proto_memsize=(clauses-unaries-binaries)*clause_extra
    +(cells-unaries-2*binaries)+clause_extra;
  min_learned=proto_memsize;
  proto_memsize+=2*binaries+learned_extra;
  if (proto_memsize>=0x80000000) {
    fprintf(stderr,"Sorry, I can't handle "O"llu cells (2^31 is my limit)!\n",
             proto_memsize);
    exit(-665);
  }
  max_cells_used=proto_memsize-learned_extra+2;
  first_learned=max_learned=min_learned+learned_extra;
  memsize=1<<memk_max;
  if (max_cells_used>memsize) {
    fprintf(stderr,
       "Immediate memory overflow (memsize="O"u<"O"u), please increase m!\n",
            memsize,max_cells_used);
    exit(-666);
  }
  if (verbose&show_details)
    fprintf(stderr,"(learned clauses begin at "O"u)\n",first_learned);
}

@ Binary data is copied temporarily into cells starting at |min_learned+2|.
(The `${}+2$' is needed because the final clause processed is input
with |c=min_learned|.)

@<Copy all the temporary cells to the |mem| and...@>=
eptr=0; /* empty the trail in preparation for unit clauses */
for (l=2;l<=max_lit;l++)
  oo,lmem[l].reason=lmem[l].watch=lmem[l].bimp_end=0;
for (c=clause_extra,j=clauses,jj=min_learned+2;j;j--) {
  k=0;
  @<Insert the cells for the literals of clause |c|@>;
  if (k<=2) @<Do special things for unary and binary clauses@>@;  
  else {
    o,size(c)=k;
    l=mem[c].lit;
    ooo,link0(c)=lmem[l].watch, lmem[l].watch=c;
    l=mem[c+1].lit;
    ooo,link1(c)=lmem[l].watch, lmem[l].watch=c;
    c+=k+clause_extra;
  }
}
if (c!=min_learned) {
  fprintf(stderr,
    "Oh oh, I didn't load the correct number of cells ("O"u:"O"u)!\n",
                   c,min_learned);
  exit(-17);
}
if (jj!=max_cells_used) {
  fprintf(stderr,
    "Oh oh, I miscounted binaries somehow ("O"u:"O"u)!\n",jj,max_cells_used);
  exit(-18);
}
@<Reformat the binary implications@>;

@ The basic idea is to ``unwind'' the steps that we went through while
building up the chunks.

@d hack_out(q) (((ullng)q)&0x3)
@d hack_clean(q) ((tmp_var*)((ullng)q&-4))

@<Insert the cells for the literals of clause |c|@>=
for (i=0;i<2;) {
  @<Move |cur_cell| back...@>;
  i=hack_out(*cur_cell);
  p=hack_clean(*cur_cell)->serial;
  p+=p+(i&1)+2;
  o,mem[c+k++].lit=p;
}

@ @<Do special things for unary and binary clauses@>=
{
  if (k<2) {
    l=mem[c].lit;
    o,vmem[thevar(l)].value=l&1,vmem[thevar(l)].plevel=0;
    oo,vmem[thevar(l)].tloc=eptr,history[eptr]=4<<28,trail[eptr++]=l;
  }@+else {
    l=mem[c].lit,ll=mem[c+1].lit; /* no mem charged for these */
    oo,lmem[bar(l)].bimp_end++;
    oo,lmem[bar(ll)].bimp_end++;
    o,mem[jj].lit=l,mem[jj+1].lit=ll,jj+=2; /* copy the literals temporarily */
  }
}

@ @<Reformat the binary implications@>=
for (l=2,jj=0;l<=max_lit;l++) {
  o,k=lmem[l].bimp_end;
  if (k)
    o,lmem[l].bimp_start=lmem[l].bimp_end=jj,jj+=k;
}
for (jj=min_learned+2,j=binaries;j;j--) {
  o,l=mem[jj].lit,ll=mem[jj+1].lit,jj+=2;
  ooo,k=lmem[bar(l)].bimp_end,bmem[k]=ll,lmem[bar(l)].bimp_end=k+1;
  ooo,k=lmem[bar(ll)].bimp_end,bmem[k]=l,lmem[bar(ll)].bimp_end=k+1;
}

@ @<Copy all the temporary variable nodes to the |vmem| array...@>=
for (c=vars; c; c--) {
  @<Move |cur_tmp_var| back...@>;
  o,vmem[c].name.lng=cur_tmp_var->name.lng;
  o,vmem[c].activity=0.0;
  o,vmem[c].stamp=0;
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

@ A few arrays aren't really of ``main'' importance, but we need to allocate
them before incorporating the clause information into |mem|.

@<Allocate the main arrays@>=
bmem=(uint*)malloc(binaries*2*sizeof(uint));
if (!bmem) {
  fprintf(stderr,"Oops, I can't allocate the bmem array!\n");
  exit(-16);
}
bytes+=binaries*2*sizeof(uint);
history=(uint*)malloc(vars*sizeof(uint));
if (!history) {
  fprintf(stderr,"Oops, I can't allocate the history array!\n");
  exit(-15);
}
bytes+=vars*sizeof(uint);

@ The other arrays can perhaps make use of the memory chunks that are
freed while we're reformatting the clause and variable data.

@<Allocate the auxiliary arrays@>=
heap=(uint*)malloc(vars*sizeof(uint));
if (!heap) {
  fprintf(stderr,"Oops, I can't allocate the heap array!\n");
  exit(-11);
}
bytes+=vars*sizeof(uint);
leveldat=(int*)malloc(vars*2*sizeof(uint));
if (!leveldat) {
  fprintf(stderr,"Oops, I can't allocate the leveldat array!\n");
  exit(-16);
}
bytes+=vars*2*sizeof(int);

@*Forcing. This program spends most of its time adding literals
to the current trail when they are forced to be true because of
earlier items on the trail.

The ``inner loop'' of the forcing phase tries to derive the
consequences of literal~|l| that follow from binary clauses in the
input. At this point |l| is a literal in the trail, and
we know that |p| is its |plevel|. Furthermore |lat=lmem[l].bimp_end|
has just been fetched, and it's known to be nonzero.

(I apologize for the awkward interface between this loop and its context.
Maybe I shouldn't worry so much about saving mems in the inner loop.
But that's the kind of guy I~am.)

@<Propagate binary implications of |l|; |goto confl| if a conflict arises@>=
for (lbptr=eptr;;) {
  for (la=lmem[l].bimp_start;la<lat;la++) {
    o,ll=bmem[la];
    if (o,isknown(ll)) {
      if (iscontrary(ll)) @<Deal with a binary conflict@>@;
      else if (o,vmem[thevar(ll)].plevel>p)
        @<Give |ll| the better reason $\bar l\lor\hbox{|ll|}$@>;
    }@+else {
      if (verbose&show_details)
        fprintf(stderr," "O"s"O".8s -> "O"s"O".8s ("O"d)\n",
                litname(l),litname(ll),p>>1);
      o,history[eptr]=4<<28,trail[eptr]=ll;
      o,vmem[thevar(ll)].plevel=p;
      o,lmem[ll].reason=-l;
      o,vmem[thevar(ll)].value=llevel+(ll&1),vmem[thevar(ll)].tloc=eptr++;
    }
  }
  while (1) {
    if (lbptr==eptr) {
      l=0;@+break; /* kludge for breaking out two levels */
    }
    o,l=trail[lbptr++];
    o,lat=lmem[l].bimp_end;
    if (lat) break;
  }
  if (l==0) break;
  o,p=vmem[thevar(l)].plevel;
}

@ @<Give |ll| the better reason $\bar l\lor\hbox{|ll|}$@>=
{
  if (verbose&show_details)
    fprintf(stderr," "O"s"O".8s -> "O"s"O".8s ("O"d*)\n",
                  litname(l),litname(ll),p>>1);
  o,lmem[ll].reason=-l;
  o,vmem[thevar(ll)].plevel=p;
}

@ @<Glob...@>=
uint lt; /* literal on the trail */
uint plt; /* its |plevel| */
uint lat; /* its |bimp_end| */
uint wa,next_wa; /* a clause in its watch list */
int nplt; /* derived |plevel| for implications */

@ The ``next to inner loop'' of forcing looks for nonbinary
clauses that have at most one literal that isn't false.

At this point we're looking at a literal |lt| that was placed on the trail,
and its |plevel| is |plt|.
Its binary implications were found at that time; now we want to examine
the more complex ones, by looking at all clauses on the watch
list of |bar(lt)|.

While doing this, we swap the first two literals, if necessary, so that
|bar(lt)| is the second one watching.

Counting of mems is a bit tricky here: If |c| is the address of a clause,
either |mem[c].lit| and |mem[c+1].lit| are in the same octabyte,
or |link0(c)| and |link1(c)|, but not both. So we make three memory
references when we're reading from or storing into all four items.

@<Propagate nonbinary implications of |lt|;
  |goto confl| if there's a conflict@>=
o,wa=lmem[bar(lt)].watch;
if (wa) {
  for (q=0;wa;wa=next_wa) {
    o,ll=mem[wa].lit;
    if (ll==bar(lt)) {
      o,ll=mem[wa+1].lit;
      oo,mem[wa].lit=ll,mem[wa+1].lit=bar(lt);
      o,next_wa=link0(wa);
      o,link0(wa)=link1(wa),link1(wa)=next_wa;
    }@+else o,next_wa=link1(wa);
    @<If clause |wa| is satisfied by |ll|, and if we don't want to
          check if |wa| improves the reason for |ll|,
          keep |wa| on the watch list and |continue|@>;
    for (o,nplt=plt,j=wa+2,jj=wa+size(wa);j<jj;j++) {
      o,ll=mem[j].lit;
      if (o,!isknown(ll) || !iscontrary(ll)) break;
      @<Update |nplt|@>;
    }
    if (j<jj) @<Swap |wa| to the watch list of |ll| and |continue|@>;
    @<Keep |wa| on the watch list@>;
    @<Force a new value, if appropriate, or |goto confl|@>;
  }
  @<Keep |wa| on the watch list@>;
}

@ @<Swap |wa| to the watch list of |ll| and |continue|@>=
{
  if (verbose&show_watches)
    fprintf(stderr," "O"s"O".8s watches "O"d\n",litname(ll),wa);
  oo,mem[wa+1].lit=ll,mem[j].lit=bar(lt);
  o,link1(wa)=lmem[ll].watch;
  o,lmem[ll].watch=wa;
  continue;
}

@ We're looking at clause |wa|, which is watched by |bar(lt)| and |ll|,
where |lt| is known to be true (at least with respect to the
decisions currently in force).

Consider what happens in the case that literal |ll| is also true,
thereby satisfying clause~|wa|: If the other
literals of |wa| turn out to be false, and if the truth
of |ll| was deduced at the current level, then |wa| might be
a better reason than we currently know for~|ll|.

This, however,
can only be the case if the |plevel| of |ll| is greater than~|plt|.
And even if that holds, a long clause will take us awhile to check;
and long clauses rarely make good reasons.

Such considerations motivate the test here, which will examine an
already-satisfied clause only if it has a reasonable chance of
becoming an improved reason for~|ll|.

@<If clause |wa| is satisfied by |ll|, and if we don't want...@>=
if ((o,isknown(ll)) && !iscontrary(ll) &&
    ((o,vmem[thevar(ll)].value<llevel) || vmem[thevar(ll)].plevel<=plt
       || (o,size(wa)>improvesize))) {
  @<Keep |wa| on the watch list@>;
  continue;
}

@ A clause |wa| can be watched by a false literal, but only if that literal
was defined on the maximum level of all literals in~|wa|.

@<Keep |wa| on the watch list@>=
if (q==0) o,lmem[bar(lt)].watch=wa;
else o,link1(q)=wa;
q=wa;

@ Well, all literals of clause |wa|, except possibly the first, did in fact
turn out to be false. Let |ll| be that first literal.

If |ll| is false, we've run into a conflict.
If |ll| is true, we've possibly found a better reason for it than
we had before.
Otherwise we will force |ll| to be true at the current decision level.

@<Force a new value, if appropriate, or |goto confl|@>=
o,ll=mem[wa].lit;
if (o,isknown(ll)) {
  if (iscontrary(ll)) @<Deal with a nonbinary conflict@>@;
  else if (o,vmem[thevar(ll)].plevel>nplt)
    @<Give |ll| the better reason |wa|@>;
}@+else {
  if (verbose&show_details)
    fprintf(stderr," "O"s"O".8s from "O"d ("O"d)\n",litname(ll),wa,nplt>>1);
  o,history[eptr]=4<<28,trail[eptr]=ll;
  o,vmem[thevar(ll)].tloc=eptr++;
  o,vmem[thevar(ll)].value=llevel+(ll&1);
  vmem[thevar(ll)].plevel=nplt;
  o,lmem[ll].reason=wa;
  o,lat=lmem[ll].bimp_end;
  if (lat) {
    l=ll,p=nplt;
    @<Propagate binary implications...@>;
  }
}

@ @<Give |ll| the better reason |wa|@>=
{
  if (verbose&show_details)
    fprintf(stderr," "O"s"O".8s from "O"d ("O"d*)\n",
              litname(ll),wa,nplt>>1);
  o,lmem[ll].reason=wa;
  o,vmem[thevar(ll)].plevel=nplt;
}

@ @<Update |nplt|@>=
if (vmem[thevar(ll)].value>=llevel) { /* |ll| is false at current level */
  if (o,vmem[thevar(ll)].plevel>nplt) nplt=vmem[thevar(ll)].plevel;
}@+else if (vmem[thevar(ll)].value>nplt) nplt=vmem[thevar(ll)].value&-2;

@ A conflict arises when both $l$ and $\bar l$ are forced to be true at the
current level. The traditional way to deal with this, if $l$ was forced first
and then~$\bar l$, is to assume that $l$ is true, and that the clause that
forces~$\bar l$ is a conflict clause.

On the other hand, we might also wish to assume that $\bar l$ is true,
and that the ``reason'' for~$l$ is a conflict clause.

If $\pi(l)=\pi(\bar l)$, according to the |plevel| theory explained earlier,
we might as well adopt the traditional attitude. But if $\pi(l)<\pi(\bar l)$,
interesting possibilities arise.

Consider, for example, clauses
$(\bar x\lor y)$,
$(\bar x\lor z)$,
$(\bar y\lor\bar a\lor w)$,
$(\bar z\lor\bar b\lor\bar w)$,
where $x$ is the decision literal at the beginning of level~30, while
$a$ was asserted at level~10 and $b$ at level~20. We compute
$\pi(x)=\pi(y)=\pi(z)=0$, $\pi(w)=10$, and $\pi(\bar w)=20$. Either
$w$ or~$\bar w$ might be encountered first, in this example, depending
on which of the binary clauses $(\bar x\lor y)$ or $(\bar x\lor z)$ we
process first. (In other examples with $\pi(w)<\pi(\bar w)$, it's
conceivable that $\bar w$ might depend on~$w$, but not that $w$
might depend on~$\bar w$.)

The traditional behavior in this case would be to learn the clause
$(\bar a\lor\bar b\lor\bar x)$, and then backtrack to level~20, where
the new clause will force $\bar x$.

But a much better policy in that example might well be to backtrack
to the end of level~10, without learning any new clause, and to relauch
level~11 with the choice variable~$x$ in place of whatever had been done
then. Then $y$, $z$, $w$, and~$\bar b$ will be deduced at level~11.
These values, together with our policy of using |oldval| for the initial
polarity of the decision literal, give us a good chance of reaching a
conflict before level~20.

I call this technique ``sliding,'' because the current level of the trail
slides down to an earlier level. Sliding is controlled by a user-specified
parameter~$s$, called |slide| in this program. If $s=0$, no sliding
is done. Otherwise we slide back to level
$\max(\pi(l)+1,\pi(\bar l)-s)$ when $\pi(l)<\pi(\bar l)$.

(As I write this, I have no idea whether sliding will be helpful or not.
It's just a hunch. In a few small test cases worked out by hand, it
seemed to stimulate active chain reactions at low-numbered levels
quite nicely; therefore I decided to take extra time and implement it here.)

Sliding can get us into an infinite loop (at least if the probability
for random decisions is zero). For example, the five clauses
$(\bar u\lor v)$,
$(\bar w\lor x)$,
$(\bar x\lor z)$,
$(\bar u\lor\bar x\lor y)$,
$(\bar v\lor\bar y\lor\bar z)$
might have us decide on~$u$, deduce~$v$, then decide on~$w$, find a
conflict and slide back to decide on~$w$ at the former level.
Then we'll deduce $x$ and~$z$, after which a decision on $x$ will
cause us to slide back again.

Therefore sliding is permitted only when it leads continually downward,
between the times when new clauses are learned.

@ In the case considered here, the conflict has arisen from a binary clause
$\bar u\lor\bar v$, where $u=l$ and $\bar v=\hbox{|ll|}$.
This clause is represented
only implicitly in the |bmem| array, not explicitly in~|mem|.
We know that $p=\pi(l)$.

@<Deal with a binary conflict@>=
{ 
  if (verbose&show_details)
    fprintf(stderr," "O"s"O".8s -> "O"s"O".8s (#"O"d)\n",
      litname(l),litname(ll),p>>1);
  o,q=vmem[thevar(ll)].plevel;
  if (q!=p && llevel<=slide_level) {
    if (q>p) nplt=q,q=p;@+else nplt=p;
    @<Slide the trail back@>@;
  }@+else {
    if (q<p) q=p;
    if (!full_run) {
      c=-l;
      goto confl;
    }
    @<Record a binary conflict@>;
  }
}

@ @<Deal with a nonbinary conflict@>=
{
  o,lll=ll,q=vmem[thevar(ll)].plevel;
  if (llevel<=slide_level) @<Set |q| to the minimum |plevel| in |wa|@>;
  if (verbose&show_details)
    fprintf(stderr," "O"s"O".8s from "O"d (#"O"d)\n",
                        litname(lll),wa,nplt>>1);
  if (q!=nplt && llevel<=slide_level) @<Slide the trail back@>@;
  else {
    if (q>nplt) q=nplt;
    if (!full_run) {
      c=wa;
      goto confl;
    }
    @<Record a nonbinary conflict@>;
  }
}

@ Since each of the literals in |wa| is false, we can use the
sliding heuristic if {\it any\/} of its new literals has a |plevel| smaller
than~|nplt|. So we find the smallest such level.

@<Set |q| to the minimum |plevel| in |wa|@>=
{
  for (o,k=wa+size(wa)-1;k>wa;k--) {
    o,l=mem[k].lit;
    if (o,vmem[thevar(l)].value>=llevel) {
      p=vmem[thevar(l)].plevel;
      if (p<q) q=p,lll=l;
    }
  }
}

@ During a ``full run,'' we continue to propagate after finding a conflict;
hence we might find many conflicts, some of which are better than others,
in the sense that their resulting conflict clause will jump back further.

We remember only one of the best, putting its clause number into
|leveldat[llevel+1]|.

The ``clause number'' of a binary clause is
considered to be |-l|, and the value of |bar(ll)| is saved
in a vacant slot of the |levstamp| array.

@<Record a binary conflict@>=
if (q<conflict_level) {
  if (verbose&show_details)
    fprintf(stderr," "O"s"O".8s -> "O"s"O".8s (@@"O"d"O"s)\n",
                  litname(l),litname(ll),q>>1,conflict_level==llevel?"":"!");
  conflict_level=q;
  o,leveldat[llevel+1]=-l;
  o,levstamp[llevel+1]=ll;
}

@ @<Record a nonbinary conflict@>=
if (q<conflict_level) {
  if (verbose&show_details)
    fprintf(stderr," "O"s"O".8s from "O"d (@@"O"d"O"s)\n",
                  litname(ll),wa,q>>1,conflict_level==llevel?"":"*");
  conflict_level=q;
  o,leveldat[llevel+1]=wa;
}

@ @<Slide the trail back@>=
{
  jumplev=q;
  if (jumplev<nplt-slide-2) jumplev=nplt-slide-2;
  oo,lt=trail[leveldat[llevel]];
  @<Enhance activities before sliding@>;
  @<Backtrack to |jumplev|@>;
  slide_level=llevel=jumplev+2;
  if (verbose&(show_choices+show_details)) {
    if (verbose&show_choices && llevel<=show_choices_max)
      fprintf(stderr,"Level "O"d, slide-trying "O"s"O".8s ("O"lld mems)\n",
              llevel>>1,litname(lt),mems);
    else fprintf(stderr,"(sliding back to level "O"d)\n",llevel>>1);
  }
  history[eptr]++;
  l=lt;
  goto launch;
}

@ Since we're going to slide over the decision literals at several levels, we
want to boost their activity scores, making them the prime candidates for
future decisions. Then they will continue to spawn the conflict that we
already know about (but hopefully at an earlier level).

@<Enhance activities before sliding@>=
debugstop(0);
for (k=nplt;k>jumplev;k-=2) {
  oo,l=trail[leveldat[k]];
  o,vmem[thevar(l)].activity=vmem[heap[0]].activity;
      /* mems in that assignment will balance out under optimization */
  @<Bump |l|'s activity@>;
}


@*Activity scores.
Experience shows that it's usually a good idea to branch on a variable that
has participated recently in the construction of conflict clauses. More
precisely, we try to maximize ``activity,'' where the activity of variable~$v$
is proportional to the sum of $\{\rho^t\mid v$ participates in the
$t\,$th-from-last conflict$\}$; here $\rho$ is a parameter representing
the rate of decay by which influential activity decays with time.
(Users can change the default ratio $\rho=.95$ if desired.)

There's a simple way to implement this quantity, because activity is
also proportional to the sum of $\{\rho^{-t}\mid v$ participates in the
$t\,$th conflict$\}$ (thus counting forward in time rather than backward).
We can therefore get proper results by adding |var_bump| to $v$'s score
whenever $v$ participates in a conflict, and then dividing |var_bump|
by~$\rho$ after each conflict.

If the activity scores computed in this way become too large, we simply
scale them back, so that relative ratios are preserved.

Incidentally, the somewhat mysterious acronym {\mc VSIDS}, which
stands for ``variable state independent decaying sum,'' is often
used by insiders to describe this aspect of a CDCL solver. The
activity scoring mechanism adopted here, due to Niklas E\'en
in the 2005 version of MiniSAT, was inspired by a
similar but less effective VSIDS scheme originally introduced
by Matthew Moskewitz in the {\mc GRAFF} solver.

@<Bump |l|'s activity@>=
v=thevar(l);
o,av=vmem[v].activity+var_bump;
o,vmem[v].activity=av;
if (av>=1e100) @<Rescale all activities@>;
o,h=vmem[v].hloc;
if (h>0) @<Sift |v| up in the heap@>;

@ When a nonzero activity is rescaled, we are careful to keep it nonzero
so that a variable once active will not take second place to a totally
inactive variable. (I doubt if this is terrifically important, but
Niklas E\'en told me that he recommends it.)

@d tiny 2.225073858507201383e-308
   /* $2^{-1022}$, the smallest positive nondenormal |double| */

@<Rescale all activities@>=
{
  for (v=1;v<=vars;v++) {
    o,av=vmem[v].activity;
    if (av)
      o,vmem[v].activity=(av*1e-100<tiny? tiny: av*1e-100);
  }
  var_bump*=1e-100;
}

@ The heap contains |hn| variables, ordered in such a way that
|vmem[x].activity>=vmem[y].activity| whenever |x=heap[h]| and
|y=heap[2*h+1]| or |y=head[2*h+2]|. In particular, |heap[0]| always
names a variable of maximum activity.

@<Sub...@>=
void print_heap(void) {
  register int k;
  for (k=0;k<hn;k++) {
    fprintf(stderr,""O"d: "O".8s "O"e\n",
        k,vmem[heap[k]].name.ch8,vmem[heap[k]].activity);
  }
}

@ @<Check the sanity of the heap@>=
for (k=1;k<=vars;k++) {
  if (vmem[k].hloc>=hn)
    fprintf(stderr,"hloc of "O".8s exceeds "O"d!\n",vmem[k].name.ch8,hn-1);
  else if (vmem[k].hloc>=0 && heap[vmem[k].hloc]!=k)
    fprintf(stderr,"hloc of "O".8s errs!\n",vmem[k].name.ch8);
}
for (k=0;k<hn;k++) {
  v=heap[k];
  if (v<=0 || v>vars)
    fprintf(stderr,"heap["O"d]="O"d!\n",k,v);
  else if (k) {
    u=heap[(k-1)>>1];
    if (u>0 && u<=vars && vmem[u].activity<vmem[v].activity)
      fprintf(stderr,"heap["O"d]act<heap["O"d]act!\n",(k-1)>>1,k);
  }
}

@ @<Sift |v| up in the heap@>=
{
  hp=(h-1)>>1; /* the ``parent'' of position |h| */
  o,u=heap[hp];
  if (o,vmem[u].activity<av) {
    while (1) {
      o,heap[h]=u;
      o,vmem[u].hloc=h;
      h=hp;
      if (h==0) break;
      hp=(h-1)>>1;
      o,u=heap[hp];
      if (o,vmem[u].activity>=av) break;
    }
    o,heap[h]=v;
    o,vmem[v].hloc=h;
    j=1;
  }
}

@ @<Put |v| into the heap@>=
{
  o,av=vmem[v].activity;
  h=hn++,j=0;
  if (h>0) @<Sift |v| up in the heap@>;
  if (j==0) oo,heap[h]=v,vmem[v].hloc=h;
}

@ With probability |rand_prob|, we select a variable from the heap at random;
this policy is a heuristic designed to avoid getting into a rut.
Otherwise we take the variable at the top, because that variable has
maximum activity.

Variables in the heap often have known values, however. If our
first choice was one of them, we keep trying from the top,
until we find |vmem[v].value==unset|.

The variable's polarity is taken from |vmem[v].oldval|, because
good values from prior experiments tend to remain good.

As in other programs of this sequence, the cost of generating
31 random bits is four mems.

@d two_to_the_31 ((unsigned long)0x80000000)

@<Choose the next decision literal, |l|@>=
mems+=4,h=gb_next_rand();
if (h<rand_prob_thresh) {
  @<Set |h| to a random integer less than |hn|@>@;
  o,v=heap[h];
  if (o,vmem[v].value!=unset) h=0;
}@+else h=0;
if (h==0) {
  while (1) {
    o,v=heap[0];
    @<Delete |v| from the heap@>;
    if (o,vmem[v].value==unset) break;
  }
}
o,l=poslit(v)+(vmem[v].oldval&1);

@ @<Set |h| to a random integer less than |hn|@>=
{
   register unsigned long t=two_to_the_31-(two_to_the_31 mod hn);
   register long r;
   do@+{
     mems+=4,r=gb_next_rand();
   }@+while (t<=(unsigned long)r);
   h=r mod hn;
}

@ Here we assume that |v=heap[0]|.

@<Delete |v| from the heap@>=
o,vmem[v].hloc=-1;
if (--hn) {
  o,u=heap[hn]; /* we'll move |u| into the ``hole'' at position 0 */
  o,au=vmem[u].activity;
  for (h=0,hp=1;hp<hn;h=hp,hp=h+h+1) {
    oo,av=vmem[heap[hp]].activity;
    if (hp+1<hn && (oo,vmem[heap[hp+1]].activity>av))
      hp++,av=vmem[heap[hp]].activity;
    if (au>=av) break;
    o,heap[h]=heap[hp];
    o,vmem[heap[hp]].hloc=h;
  }      
  o,heap[h]=u;
  o,vmem[u].hloc=h;
}

@ At the very beginning, all activity scores are zero.
We'll permute the variables randomly in |heap|, for the sake of variety.

@<Initialize the heap@>=
for (k=1;k<=vars;k++) o,heap[k-1]=k;
for (hn=vars;hn>1;) {
  @<Set |h| to a random integer less than |hn|@>;
  hn--;
  if (h!=hn) {
    o,k=heap[h];
    ooo,heap[h]=heap[hn],heap[hn]=k;
  }
}
for (h=0;h<vars;h++) {
  o,v=heap[h];
  o,vmem[v].hloc=h,vmem[v].oldval=1;
}
hn=vars;

@ Learned clauses also have activity scores. They aren't used as
heavily as the scores for variables; we look at them only when
deciding what clauses to keep after too many learned clauses
have accumulated.

@<Bump |c|'s activity@>=
{
  float ac;
  o,ac=clause_act(c)+clause_bump;
  o,clause_act(c)=ac;
  if (ac>=1e20) @<Rescale all clause activities@>;
}

@ @d single_tiny 1.1754943508222875080e-38
  /* $2^{-126}$, the smallest positive nondenormal |float| */

@<Rescale all clause activities@>=
{
  for (k=first_learned;k<max_learned;o,k+=size(k)+clause_extra+learned_extra) {
    o,ac=clause_act(k);
    if (ac)
      o,clause_act(k)=(ac*1e-20<single_tiny? single_tiny: ac*1e-20);
  }
  clause_bump*=1e-20;
}

@ @<Glob...@>=
double var_bump=1.0;
float clause_bump=1.0;
double var_bump_factor; /* reciprocal of |var_rho| */
float clause_bump_factor; /* reciprocal of |clause_rho| */

@ @<Bump the bumps@>=
var_bump*=var_bump_factor;
clause_bump*=clause_bump_factor;

@*Learning from a conflict.
A conflict arises when some clause is found to have no true literals
at the current level. This program relies on a technique for converting
such a conflict into a new clause that is worth learning. Our current
goal is to implement (and thereby to understand) that technique.

Let's say that a literal is ``new'' if it has become true or false at
the current decision level; otherwise it is ``old.'' A conflict must
contain at least two new literals, because we don't start a new level
until every unsatisfied clause is watched by two unassigned literals.

(Hedge: In a ``full run'' we march boldly into deeper levels after
finding conflicts; and in such cases the conflict clauses of level~$d$
are watched by two literals that are false at level~$d$. However,
even in this case, every unsatisfied clause that could lead to a
conflict at a deeper level is watched by two unassigned literals.)

Suppose all literals of $c$ are false. If $\bar l\in c$ and $c'$ is the
reason for $l$, we can resolve $c$ with~$c'$ to get a new clause~$c''$.
This clause~$c''$ is obtained from~$c$ by deleting~$\bar l$ and
then inserting $\bar l'$ for all $l'$ such that $l\succ l'$. (Indeed,
when introducing the method of conflict-driven clause learning above,
we defined this direct dependency relation by saying that $l\succ l'$ if and
only if $\bar l'$ appears in the reason for~$l$.)
Notice that all of the literals that belong to $c''$ are false;
hence $c''$, like~$c$, represents a conflict.

The partial ordering $\succ$ can be topologically sorted into a
linear ordering~$>$, so that $l>l'$ whenever $l\succ l'$. If $c$
contains more than one new literal, its largest $\bar l$ must therefore
have a reason. (Only a decision literal has no reason; the current decision
literal can't be largest, because every other new literal depends on it.)
Thus the largest literal in~$c''$ will be smaller than~$l$ in the
linear ordering.

By starting with a conflict clause $c$ and repeatedly
resolving away the largest literal, it follows that we'll eventually obtain
a clause~$c_0$ that has only one new literal. And if $c_0$ was derived by
resolving with other clauses $c_1$, \dots,~$c_k$, the old literals of $c_0$
will be the old literals of $c$, $c_1$, \dots,~$c_k$.

We could now learn the clause $c_0$, and return to decision level~$d$,
the maximum of the levels of $c_0$'s old literals. (Its new literal
will now be forced false at that level.)

Actually, we'll try to simplify $c_0$ before learning it,
by removing some of its old literals if they are redundant. But that's
another story, which we can safely postpone until later. The main idea
is this: Starting with a conflict clause~$c$, containing two or more new
literals, we boil it down to a clause~$c_0$ that contains only one.
Then we can resume at a previous level.

@ If we always stick with the {\it first\/} reason that propagation
finds for any particular literal, the process described above will be
quite easy to visualize, because $l'$ will occur earlier in the trail
than~$l$ whenever $l\succ l'$.

But a literal might be forced true by many different clauses, and
some of those clauses might make much more satisfactory reasons than others.
We see the clauses one at a time, as we examine watch lists. And we'll
probably prefer a newly encountered clause $c$ to a previously seen clause~$c'$,
if $c'$ has an old literal on decision level 20 while every old literal
depended upon by the literals of~$c$ has decision level 10 or less.

Let's say that the ``back-jump level'' of the learned clause~$c_0$ is the
largest level of an old literal in~$c_0$. A small back-jump level
is preferable to a large one; so this program tries to minimize it, by
changing a literal's reason when the new reason has a decent chance of
producing a smaller back-jump level.

The |plevel| of a literal, $\pi(l)$, is an upper bound on the back-jump level
that will arise when $l$ appears in a conflict clause. Our program above
for the forcing algorithm computes that bound by setting
$\pi(l)=0$ if $l$ is a decision literal; otherwise, if the reason for~$l$
is $l\lor\bar l_1\lor\cdots\lor\bar l_k$, we set $\pi(l)=\max\bigl(
\pi'(l_1),\ldots,\pi'(l_k)\bigr)$, where $\pi'(l)$ denotes $\pi(l)$ when $l$
is new and $\pi'(l)$ denotes the level of~$l$ when $l$ is old.

Our program also changes the reason for $l$ if we encounter a new reason
that will make $\pi(l)$ smaller, according to this definition. Such a change
is somewhat drastic, because a different reason means that we have a
different dependency relation: Once we change that relation, some dependencies
go away, while others materialize. Moreover, when we change $\pi(l)$, the
equation $\pi(l')=\max\bigl(\pi'(l'_1),\ldots,\pi'(l'_{k'})\bigr)$ that
we had used to define the $\pi$ value of
{\it another\/} literal~$l'$ may no longer hold.

However, the fact that $\pi$ never gets bigger allows us to sure that the
inequality
$$\pi(l')\;\ge\;\max\bigl(\pi'(l'_1),\ldots,\pi'(l'_{k'})\bigr)$$
does remain valid. Consequently the fundamental inequality
$$\pi(l)\ge\pi'(l')\qquad\hbox{whenever $l\sucp l'$}$$
holds both before and after every change to the dependency relation.

If $l$ receives a new reason $l\lor\bar l_1\lor\cdots\lor\bar l_k$ in
place of its former one, thereby changing $\pi(l)$ from $p$ to $p'<p$,
the change in dependencies cannot introduce a circularity $l\sucp l$.
For if $l_j\sucp l$ were true for any~$j$, we would have
$\pi'(l_j)\ge\pi'(l)=p$ before the change, contradicting the fact
that $p'=\max\bigl(\pi'(l_1),\ldots,\pi'(l_k)\bigr)<\pi'(l)=p$.

Notice furthermore that a conflict clause $\bar l_1\lor\cdots\lor\bar l_k$
will lead to a back-jump level less than or equal to
$\max\bigl(\pi(l_1),\ldots,\pi(l_k)\bigr)$ as we resolve new literals away.
Therefore some conflict clauses might be much better than others. When
this program does a ``full run'' (as explained further below), it therefore
selects a conflict clause that minimizes this bound, instead of immediately
learning a clause from the first conflict that happens to appear.

@ So much for theory; let's proceed to practice. We can use the |stamp|
field to identify literals that appear in the conflict clause~$c$, or in the
clauses derived from~$c$ as we compute~$c_0$: A variable's |stamp| will
equal |curstamp| if and only if we have just marked it.

The algorithm for computing $c_0$ requires us to identify the literal
of the current conflict clause that is {\it largest}, in some
unspecified linear order that could be obtained by topological sorting of the
dependency relation. Unfortunately the dependency relation might be very large,
involving quite a few new literals; and we might be interested in
only a few of those literals. So we don't want to take the time to compute a
topological order, even though topological sorting can be done in
linear time.

Suppose we opt instead to use a simpler algorithm that doesn't need
to know the largest literal. If we just resolve away {\it any\/} literal
that has a current reason, we will eventually come up with a clause $c_0'$ that
contains only a single new literal. We could learn it. Unfortunately, however,
$c_0'$ might not be the best one to learn.

For example, consider the reason clauses $l_1\lor\bar l_0\lor\bar a_1$ and
$l_2\lor\bar l_1\lor\bar a_2$, and the conflict clause
$\bar l_2\lor\bar l_1\lor\bar a_3$, where $a_1$, $a_2$, and $a_3$ are old.
The decision literal is~$l_0$.
If we resolve first with the reason for~$l_1$, we get
$\bar l_2\lor\bar l_0\lor\bar a_1\lor\bar a_3$; then we resolve with the
reason for~$l_2$ and get the learnable clause $c_0'=\bar l_0\lor\bar a_1\lor
\bar a_2\lor\bar a_3$. But if we had first removed $l_2$ (as required
by the stated algorithm because $l_2\succ l_1$), we would have obtained
the much better clause $c_0=\bar l_1\lor\bar a_2\lor\bar a_3$.

Thus it's generally best to resolve away a literal that is maximal with
respect to the $\sucp$ relation. The program below tries to guess such
a literal by using the trail location |tloc| as an approximation to
topological order: It marches backwards in the trail in order of
decreasing~|tloc|, setting |stamp| fields
to mark the relevant literals, and going the other direction only
in the relatively rare cases when trail order is violated. More
precisely, if we've already dealt with all marked items whose |tloc|
is less than~|t|, and if we discover that a literal with |tloc>=t| needs
to be marked, we put that literal (and any of its offspring that also
have |tloc>=t|) onto a stack;
and we use brute force to clear out that stack as soon as we can. This
approach doesn't always find the best~$c_0$. But --- knock on wood ---
it probably does pretty well.

Incidentally, the example above also indicates the crudity of our
$\pi(l)$ heuristic: The $\pi$ values of $l_1$ and $l_2$ will necessarily
be at least the level of~$a_1$, although the best $c_0$ doesn't involve~$a_1$
at all. Indeed, this program doesn't use $\pi(l)$ because that number is optimal
in any sense. We compute |plevel|, and try to improve reasons, only
because the amount of extra work is plausibly smaller than the amount
of payoff, in typical problems. (As I write this paragraph, I can hardly wait
to see what will happen. Who knows? Algorithms for satisfiability are
notoriously unpredictable.)

@<Deal with the conflict clause |c|@>=
oldptr=jumplev=xnew=clevels=0;
@<Bump |curstamp| to a new value@>;
if (verbose&show_gory_details)
  fprintf(stderr,"Preparing to learn");
if (c<0) @<Initialize a binary conflict@>@;
else @<Initialize a nonbinary conflict@>;
@<Reduce |xnew| to zero@>;
if (stackptr) o,l=stack[0]; /* |stackptr| must be 1 in this case */
else@+while (1) {
  o,l=trail[tl--];
  if (o,vmem[thevar(l)].stamp==curstamp) break;
}
lll=bar(l); /* |lll| will complete the learned clause */  
if (verbose&show_gory_details)
  fprintf(stderr," "O"s"O".8s\n",litname(lll));

@ @<Initialize a nonbinary conflict@>=
{
  if (c>min_learned) @<Bump |c|'s activity@>;
  o,s=size(c);
  o,l=bar(mem[c].lit);
  o,tl=vmem[thevar(l)].tloc;
  o,vmem[thevar(l)].stamp=curstamp;
  @<Bump |l|'s activity@>;
  for (k=c+s-1;k>c;k--) {
    o,l=bar(mem[k].lit);
    o,vmem[thevar(l)].stamp=curstamp;
    @<Bump |l|'s activity@>;
    o,j=vmem[thevar(l)].tloc;
    if (j>tl) tl=j;
    o,j=vmem[thevar(l)].value&-2;
    if (j>=llevel) xnew++;
    else if (j) {
      if (j>jumplev) jumplev=j;
      o,learn[oldptr++]=bar(l);
      if (verbose&show_gory_details)
        fprintf(stderr," "O"s"O".8s",litname(bar(l)));
      if (o,levstamp[j]<curstamp) o,levstamp[j]=curstamp,clevels++;
      else if (levstamp[j]==curstamp) o,levstamp[j]=curstamp+1;
    }
  }
}

@ Here the conflict is that |l| implies |ll|, where literal |l=-c| is
true but literal |ll| is false.

@<Initialize a binary conflict@>=
{
  o,tl=vmem[thevar(ll)].tloc;
  o,vmem[thevar(ll)].stamp=curstamp;
  l=ll;
  @<Bump |l|'s activity@>;
  l=-c;
  if (o,vmem[thevar(l)].tloc>tl) tl=vmem[thevar(l)].tloc;
  o,vmem[thevar(l)].stamp=curstamp;
  @<Bump |l|'s activity@>;
  xnew=1;  
}

@ @<Allocate the auxiliary arrays@>=
learn=(uint*)malloc(vars*sizeof(uint));
if (!learn) {
  fprintf(stderr,"Oops, I can't allocate the learn array!\n");
  exit(-16);
}
bytes+=vars*sizeof(uint);

@ @<Glob...@>=
uint curstamp; /* a unique value for marking literals and levels of interest */
uint *learn; /* literals in a clause being learned */
int oldptr; /* this many old literals contributed to learned clause so far */
int jumplev; /* level to which we'll return after learning */
int slide_level; /* upper bound on level from which sliding is permitted */
int tl; /* trail location for examination of stamped literals */
int xnew; /* excess new literals in the current conflict clause */
int clevels; /* levels represented in the current conflict clause */
int stackptr; /* number of elements in the stack */
int learned_size; /* number of literals in the learned clause */
int trivial_learning; /* does the learned clause involve every decision? */

@ The algorithm that follows will use |curstamp|, |curstamp+1|, and
|curstamp+2|.

@<Bump |curstamp| to a new value@>=
if (curstamp>=0xfffffffe) {
  for (k=1;k<=vars;k++) oo,vmem[k].stamp=levstamp[k+k-2]=0;
  curstamp=1;
}@+else curstamp+=3;

@ @<Reduce |xnew| to zero@>=
stackptr=0;
while (xnew) {
  if (stackptr) o,l=stack[--stackptr];
  else@+while (1) {
    o,l=trail[tl--];
    if (o,vmem[thevar(l)].stamp==curstamp) break;
  }
  xnew--;
  @<Resolve with the reason of |l|@>;
}

@ At this point the current conflict clause is represented implicitly
as the set of negatives of the literals |trail[j]| for |j<=tl| that
have |stamp=curstamp|, together with |stackptr| other literals that appear in
the stack, together with |bar(l)|. Old literals in that set are in the |learn|
array. The conflict clause contains exactly
|xnew+1| new literals besides |bar(l)|; we will replace |bar(l)|
by the other literals in |l|'s reason.

@<Resolve with the reason of |l|@>=
if (verbose&show_gory_details)
  fprintf(stderr," ["O"s"O".8s]",litname(l));
o,c=lmem[l].reason;
if (c<0) @<Resolve with binary reason@>@;
else if (c) { /* |l=mem[c].lit| */
  if (c>=min_learned) @<Bump |c|'s activity@>;
  for (o,k=c+size(c)-1;k>c;k--) {
    o,l=bar(mem[k].lit);
    if (o,vmem[thevar(l)].stamp!=curstamp)
      @<Stamp |l| as part of the conflict clause milieu@>;
  }
}

@ @<Resolve with binary reason@>=
{
  l=-c;
  if (o,vmem[thevar(l)].stamp!=curstamp)
    @<Stamp |l| as part of the conflict clause milieu@>;
}

@ @<Stamp |l| as part of the conflict clause milieu@>=
{
  o,vmem[thevar(l)].stamp=curstamp;
  @<Bump |l|'s activity@>;
  if (vmem[thevar(l)].tloc>tl) {
    xnew++; /* this literal must be new, since it's high in the trail */
    o,stack[stackptr++]=l;
  }@+else {
    o,j=vmem[thevar(l)].value&-2;
    if (j>=llevel) xnew++;
    else if (j) {
      if (j>=jumplev) jumplev=j;
      o,learn[oldptr++]=bar(l);
      if (verbose&show_gory_details)
        fprintf(stderr," "O"s"O".8s",litname(bar(l)));
      if (o,levstamp[j]<curstamp) o,levstamp[j]=curstamp,clevels++;
      else if (levstamp[j]==curstamp) o,levstamp[j]=curstamp+1;
    }
  }
}
@ The |stack| and |levstamp| arrays have
enough room for twice the number of variables, because
we use them for dual purposes below.

@<Allocate the auxiliary arrays@>=
stack=(int*)malloc(vars*2*sizeof(int));
if (!stack) {
  fprintf(stderr,"Oops, I can't allocate the stack array!\n");
  exit(-16);
}
bytes+=vars*2*sizeof(int);
levstamp=(uint*)malloc(2*vars*sizeof(uint));
if (!levstamp) {
  fprintf(stderr,"Oops, I can't allocate the levstamp array!\n");
  exit(-16);
}
bytes+=2*vars*sizeof(uint);
for (k=0;k<vars;k++) o,levstamp[k+k]=0;

@ @<Glob...@>=
int *stack; /* place for homemade recursion control */
uint *levstamp; /* memos for recursive answers; also binary conflict info */

@*Simplifying the learned clause.
Suppose the clause to be learned is $\bar l\lor\bar a_1\lor\cdots\lor\bar a_k$.
Many of the literals $\bar a_j$ often turn out to be redundant, in the sense
that a few well-chosen resolutions will remove them.

For example, if the reason of $a_4$ is $a_4\lor\bar a_1\lor\bar b_1$ and
the reason of~$b_1$ is $b_1\lor\bar a_2\lor\bar b_2$ and the reason of~$b_2$
is $b_2\lor\bar a_1\lor\bar a_3$, then $\bar a_4$ is redundant.

Niklas S\"orensson, one of the authors of MiniSAT, noticed that learned
clauses could typically be shortened by 30\% when such simplifications are
made. Therefore we certainly want to look for removable literals, even though
the algorithm for doing so is somewhat tricky.

The literal $\bar a$ is redundant in the clause-to-be-learned if and only if
the other literals in its reason are either present in that clause
or (recursively) redundant. (In the example above we must check that
$\bar a_1$ and $\bar b_1$ satisfy this condition; that boils down to
observing that $\bar b_1$ is redundant, because $\bar b_2$ is redundant.)

Since the relation $\sucp$ is a partial ordering, we can determine
redundancy by using a ``bottom up'' method with this recursive definition.
Or we can go ``top down'' with memoization (which is what we'll do):
We shall stamp a literal $b$ with |curstamp+1| if $\bar b$ is known to
be redundant, and with |curstamp+2| if $\bar b$ is known to be nonredundant.
Once we know a literal's status, we won't need to apply the recursive
definition again.

A nice trick (also due to S\"orensson) can be used to speed this process up,
using the fact that a non-decision literal always depends on at least one
other literal at the same level: A literal $\bar a_j$ can be redundant
only if it shares a level with some other literal $\bar a_i$ in the
learned clause. Furthermore, a literal $\bar b$ not in that clause can be
redundant only if it shares a level with some~$\bar a_j$.

A careful reader of the code in the previous sections will have noticed
that we've set |levstamp[t+t]=curstamp| if level~|t| contains exactly one
of the literals $\bar a_j$, and we've set |levstamp[t+t]=curstamp+1|
if it contains more than one. Those facts will help us decide non-redundancy
without pursuing the whole recursion into impossible levels.

@ Instead of doing this computation with a recursive procedure, I want
to control the counting of memory accesses, and to take advantage of
the special logical structure that's present. So the program here uses an
explicit stack to hold the parameters of unfinished queries.

When we enter this section, |stackptr| will be zero (it says here).
When we leave it, whether by going to |redundant| or not,
the original value of~|l| will be in~|ll|.
I~think this loop makes an instructive
example of how recursion relates to iteration.

One can prove inductively that, at label |test|, we have
|vmem[thevar(l)].stamp<=curstamp|, with equality if and only if |stackptr=0|.

@<If $\bar l$ is redundant, |goto redundant|@>=
if (stackptr) confusion("stack");
test: ll=l;
o,c=lmem[l].reason;
if (c==0) goto clear_stack; /* decision literal is never redundant */
if (c<0) { /* binary reason */
  l=bar(-c);
  o,s=vmem[thevar(l)].stamp;
  if (s>=curstamp) {
    if (s==curstamp+2) goto clear_stack; /* known non-redundant */
  }@+else {
    o,stack[stackptr++]=ll;
    goto test;
  }
}@+else {
  for (o,k=c+size(c)-1;k>c;k--) {
    o,l=bar(mem[k].lit);
    o,s=vmem[thevar(l)].stamp;
    if (s>=curstamp) {
      if (s==curstamp+2) goto clear_stack; /* known non-redundant */
      continue;
    }
    oo,s=levstamp[vmem[thevar(l)].value&-2];
    if (s<curstamp) { /* the level is bad */
      o,vmem[thevar(l)].stamp=curstamp+2;
      goto clear_stack;
    }
    o,stack[stackptr]=k, stack[stackptr+1]=ll, stackptr+=2;
    goto test;
test1:@+continue;
  }
}
is_red: o,vmem[thevar(ll)].stamp=curstamp+1;
    /* we've proved |bar(ll)| redundant */
if (stackptr) {
  o,ll=stack[--stackptr];
  o,c=lmem[ll].reason;
  if (c<0) goto is_red;
  o,k=stack[--stackptr];
  goto test1; /* jump back into the loop */
}
goto redundant;
@<Clear the stack@>;

@ If any of the literals we encounter during that recursive exploration
are non-redundant, the literal |ll| we're currently working on is
non-redundant, and so are all of the literals on the stack.

(The literal at the bottom of the stack belongs to the learned clause,
so we keep its stamp equal to |curstamp|. The other literals, whose
stamp was less than |curstamp|, are now marked with |curstamp+2|.)

@<Clear the stack@>=
clear_stack:@+if (stackptr) {
  o,vmem[thevar(ll)].stamp=curstamp+2;
  o,ll=stack[--stackptr];
  o,c=lmem[ll].reason;
  if (c>0) stackptr--;
  goto clear_stack;
}

@ Sometimes the learned clause turns out to be unnecessarily long even
after we simplify it. This can happen, for example, if the decision
literal~|l| on level~1 is not part of the clause, but all the other literals
have a reason that depends on~|l|; then no literal is redundant, by our
definitions, yet many literals can be from the same level.

If the learned clause size exceeds the jump level plus~1, we replace it
by a ``trivial'' clause based on decision literals only. (In such cases
we are essentially doing no better than an ordinary backtrack algorithm.)

@<Simplify the learned clause@>=
learned_size=oldptr+1;
cells_prelearned+=learned_size;
for (kk=0;kk<oldptr;kk++) {
  o,l=bar(learn[kk]);
  oo,s=levstamp[vmem[thevar(l)].value&-2];
  if (s<curstamp+1) continue; /* |l|'s level doesn't support redundancy */
  @<If $\bar l$ is redundant, |goto redundant|@>;
  continue;
redundant: learned_size--;
  if (verbose&show_gory_details) /* note that |l| has been moved to |ll| */
    fprintf(stderr,"("O"s"O".8s is redundant)\n",litname(bar(ll)));
}
if (learned_size<=(jumplev>>1)+1) trivial_learning=0;
else trivial_learning=1,clevels=jumplev>>1,learned_size=clevels+1,trivials++;
cells_learned+=learned_size,total_learned++;

@ The following code is used only when |learned_size>1|. (Learned
unit clauses are, of course, happy events; but we deal with them separately.)

The new clause must be watched by two literals. One literal in this
clause, namely~|lll|, was formerly false but it will become true.
It's the one that survived from the conflict
on the active level, and it will be one of the watchers we need.

All other literals in the learned clause are currently false. We must
choose one of those on the highest level (furthest from root level)
to be a watcher. For if we don't, backtracking might take us to
a lower level on which the clause becomes forcing, yet we don't
see that fact --- we're not watching it! (The true literal and
an unwatched literal become unassigned. Then, if the unwatched literal
becomes false, we don't notice that the formerly true literal
is now forced true again.)

@<Learn the simplified clause@>=
{
  @<Determine the address, |c|, for the learned clause@>;
  @<Store the learned clause |c|@>;
  if (learned_file) @<Output |c| to the file of learned clauses@>;
  o,vmem[thevar(lll)].value=jumplev+(lll&1),vmem[thevar(lll)].plevel=p;
  o,lmem[lll].reason=c;
  if (verbose&(show_details+show_choices)) {
    if ((verbose&show_details) || llevel<=show_choices_max)
      fprintf(stderr,"level "O"d, "O"s"O".8s from "O"d ("O"d)\n",
         jumplev>>1,litname(lll),c,p>>1);
  }
}

@ In early runs of this program, I noticed several times when the previously
learned clause is immediately subsumed by the next clause to be learned.
On further inspection, it turned out that this happened when the
previously learned clause was the reason for a literal on a level that
is going away (because |jumplev| is smaller).

So I now check for this case. Backtracking has already zeroed out this
literal's reason.

@<Determine the address, |c|, for the learned clause@>=
if (prev_learned) {
  o,l=mem[prev_learned].lit;
  if (o,lmem[l].reason==0)
    @<Discard clause |prev_learned| if it is subsumed by
           the current learned clause@>;
}
c=max_learned; /* this will be the address of the new clause */
max_learned+=learned_size+clause_extra+learned_extra;
if (max_learned>max_cells_used) {
  max_cells_used=max_learned;
  if (max_cells_used>=memsize) {
    fprintf(stderr,
       "Memory overflow (memsize="O"u<"O"u), please increase m!\n",
            memsize,max_cells_used);
    exit(-666);
  }
}
prev_learned=c;

@ The first literal of |prev_learned| was true at its level, so it isn't
part of the conflict clause. We will discard |prev_learned| if all
literals of the learned clause appear among the {\it other\/} literals of
|prev_learned|.

@<Discard clause |prev_learned| if it is subsumed by...@>=
{
  for (o,k=size(prev_learned)-1,q=learned_size;q && k>=q;k--) {
    oo,l=mem[prev_learned+k].lit,r=vmem[thevar(l)].value&-2;
    if (r<=jumplev) {
      if (trivial_learning) {
        if (o,lmem[l].reason==0) q--;
      }@+else if (o,vmem[thevar(l)].stamp==curstamp) q--;
          /* yes, |l| is in the learned clause */
    }
  }
  if (q==0) {
      max_learned=prev_learned; /* forget the previously learned clause */
      if (verbose&show_gory_details)
        fprintf(stderr,"(clause "O"d discarded)\n",prev_learned);
      discards++;
      o,l=mem[prev_learned].lit;
      @<Remove |prev_learned| from |l|'s watch list@>;
      o,l=mem[prev_learned+1].lit;
      @<Remove |prev_learned| from |l|'s watch list@>;
  }
}

@ @<Remove |prev_learned| from |l|'s watch list@>=
for (o,wa=lmem[l].watch,q=0;wa;q=wa,r=t,wa=next_wa) {
  o,p=mem[wa].lit;
  t=(p==l? 0: 1);
  o,next_wa=link0(wa-t);
  if (wa==prev_learned) {
    if (q) o,link0(q-r)=next_wa;
    else o,lmem[l].watch=next_wa;
    break;
  }
}
if (wa==0) confusion("discard");

@ Here we also compute $p=\pi(\hbox{|lll|})$.

@<Store the learned clause |c|@>=
o,size(c)=learned_size;
o,clause_act(c)=0.0,levels(c)=clevels;
  /* no mem need be charged here, since we're charging for |link0|, |link1| */
o,mem[c].lit=lll;
oo,link0(c)=lmem[lll].watch;
o,lmem[lll].watch=c;
if (trivial_learning) {
  for (j=1,k=jumplev;k;j++,k-=2) {
    oo,l=bar(trail[leveldat[k]]);
    if (j==1) ooo,link1(c)=lmem[l].watch,lmem[l].watch=c;
    o,mem[c+j].lit=l;
  }
  p=jumplev-2;
  if (verbose&show_gory_details)
    fprintf(stderr,"(trivial clause is substituted)\n");
}@+else for (k=1,p=j=0,jj=1;k<learned_size;j++) {
  o,l=learn[j];
  if (o,vmem[thevar(l)].stamp==curstamp) { /* not redundant */
    o,r=vmem[thevar(l)].value;
    if (vmem[thevar(l)].value>=jumplev) { /* we're computing $\pi'(l)$ */
      if (vmem[thevar(l)].plevel>p) p=vmem[thevar(l)].plevel;
    }@+else if (r>p) p=r&-2;
    if (jj && r>=jumplev) {
      o,mem[c+1].lit=l;      
      oo,link1(c)=lmem[l].watch;
      o,lmem[l].watch=c;
      jj=0;
    }@+else o,mem[c+k+jj].lit=l;
    k++;
  }
}

@ @<Output |c| to the file of learned clauses@>=
{
  for (k=c; k<c+learned_size; k++)
    fprintf(learned_file," "O"s"O".8s",litname(mem[k].lit));
  fprintf(learned_file,"\n");
  fflush(learned_file);
}

@*Putting it all together.
Most of the mechanisms that we need to solve a satisfiability problem
are now in place. We just need to set them in motion at the proper times.

@<Solve the problem@>=
@<Finish the initialization@>;
llevel=0;
if (sanity_checking) sanity(eptr);
lptr=0;
proceed:@+@<Complete the current level, or |goto confl|@>;
newlevel:@+if (sanity_checking) sanity(eptr);
if (eptr==vars) goto satisfied;
if (delta && (mems>=thresh)) thresh+=delta,print_state(eptr);
llevel+=2;
@<Choose the next decision...@>;
if (verbose&show_choices && llevel<=show_choices_max)
  fprintf(stderr,"Level "O"d, trying "O"s"O".8s ("O"lld mems)\n",
          llevel>>1,litname(l),mems);
o,lmem[l].reason=0;
history[eptr]=0;
launch: nodes++;
o,leveldat[llevel]=eptr;
o,trail[eptr++]=l;
o,vmem[thevar(l)].tloc=lptr; /* |lptr=eptr-1| */
o,vmem[thevar(l)].value=llevel+(l&1), vmem[thevar(l)].plevel=0;
conflict_level=llevel;
goto proceed;
confl:@+if (llevel) {
  @<Deal with the conflict clause |c|@>;
  @<Simplify the learned clause@>;
   /* Note: |lll| is the false literal that will become true */
  decisionvar=(lmem[bar(lll)].reason? 0: 1); /* was it first in its level? */
  @<Backtrack to |jumplev|@>;
  if (slide) slide_level=jumplev;
  if (learned_size>1) @<Learn the simplified clause@>@;
  else @<Learn a clause of size 1@>;
  history[eptr]=(decisionvar? 2: 6)<<28;
  o,trail[eptr++]=lll;
  o,vmem[thevar(lll)].tloc=lptr; /* |lptr=eptr-1| */
  @<Bump the bumps@>;
  if (sanity_checking) sanity(eptr);
  goto proceed;
}
if (1) printf("~\n"); /* the formula was unsatisfiable */
else {
satisfied: @<Print the solution found@>;
}

@ @<Learn a clause of size 1@>=
{
  if (verbose&(show_details+show_choices))
    fprintf(stderr,"level 0, learned "O"s"O".8s\n",litname(lll));
  o,vmem[thevar(lll)].value=lll&1;
  if (learned_file) fprintf(learned_file," "O"s"O".8s\n",litname(lll));
}


@ @<Complete the current level, or |goto confl|@>=
ebptr=eptr; /* binary implications needn't be checked after this point */
while (lptr<eptr) {
  o,lt=trail[lptr++];
  o,plt=vmem[thevar(lt)].plevel;
  if (lptr<=ebptr) {
    o,lat=lmem[lt].bimp_end;
    if (lat) {
      l=lt,p=plt;
      @<Propagate binary...@>;
    }
  }
  @<Propagate nonbinary...@>;
}

@ @<Backtrack to |jumplev|@>=
o,k=leveldat[jumplev+2];
while (eptr>k) {
  o,l=trail[--eptr],v=thevar(l);
  oo,vmem[v].oldval=vmem[v].value;
  o,vmem[v].value=unset;
  o,lmem[l].reason=0;
  if (eptr<lptr && (o,vmem[v].hloc<0)) @<Put |v| into the heap@>;
}
lptr=eptr;
if (sanity_checking) {
  while (llevel>jumplev) leveldat[llevel]=-1,llevel-=2;
}@+else llevel=jumplev;

@ @<Print the solution found@>=
for (k=0;k<vars;k++) {
  o,printf(" "O"s"O".8s",litname(trail[k]));
}
printf("\n");
if (out_file) {
  for (k=0;k<vars;k++) {
    o,fprintf(out_file," "O"s"O".8s",litname(bar(trail[k])));
  }
  fprintf(out_file,"\n");
  fprintf(stderr,"Solution-avoiding clause written to file `"O"s'.\n",out_name);
}

@ @<Finish the initialization@>=
if (slide==0) slide_level=0;
if (rand_prob>=1.0) rand_prob_thresh=0x80000000;
else rand_prob_thresh=(int)(rand_prob*2147483648.0);
var_bump_factor=1.0/(double)var_rho;
clause_bump_factor=1.0/clause_rho;
show_choices_max<<=1,slide<<=1; /* double the level-oriented parameters */
if (verbose&show_details) {
  for (k=0;k<eptr;k++)
      fprintf(stderr,""O"s"O".8s is given\n",litname(trail[k]));
}
for (k=0;k<vars;k++) o,leveldat[k+k]=-1,leveldat[k+k+1]=0;

@ @<Subr...@>=
void confusion(char *id) { /* an assertion has failed */
  fprintf(stderr,"This can't happen ("O"s)!\n",id);
  exit(-666);
}
@#
void debugstop(int foo) { /* can be inserted as a special breakpoint */
  fprintf(stderr,"You rang("O"d)?\n",foo);
}

@ @<Glob...@>=
uint full_run; /* are we making a pass to gather data on all variables? */
uint conflict_level; /* smallest backjump level so far for conflicts */
uint decisionvar; /* does the learned clause involve the decision literal? */
uint prev_learned; /* number of the clause most recently learned */

@*Index.
