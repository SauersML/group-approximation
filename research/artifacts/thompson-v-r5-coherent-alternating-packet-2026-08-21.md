# The Bleak--Quick R5 cell and coherent alternating packets in Thompson V

**Date:** 2026-08-21

This note isolates a concrete sufficient mechanism for the open bare-Thompson
one-word Hilbert--Schmidt ceiling.  The implication from the mechanism to
nonhyperlinearity is complete.  The mechanism itself, called coherent
alternating-packet synchronization below, is open.

## 1. The finite presentation and the distinguished R5 source

Bleak and Quick, *The infinite simple group V of Richard J. Thompson:
presentations by permutations*, Groups Geom. Dyn. 11 (2017), 1401--1436,
arXiv:1511.02123, prove a finite presentation of `V` by prefix transpositions.
In their notation the five displayed families are

```text
R1: (00 01)^2=(01 10 11)^3=((00 01)(01 10 11))^4=1,
R2: (1 01)^(1 00)=(00 01),
R3: (1 00)=(10 000)(11 001),
R4: [(00 010),(10 111)]=[(00 011),(10 111)]=1,
R5: [(000 010),(10 110)]=1.
```

Here `(alpha beta)` is the homeomorphism interchanging the two incomparable
binary cylinders `alpha*` and `beta*`.  The proof uses R5 as the seed for the
last disjoint-support orbit, the case involving three distinct length-two
prefixes.  R1 is the local finite permutation packet, R2 transports names,
R3 splits one prefix swap into two finer disjoint swaps, and R4 treats the two
earlier disjoint-support types.  Thus R5 is the first plausible collision cell
not present in the pure binary-clone fragment.

The paper proves enough relations through depth three to verify a fixed
Cannon--Floyd--Parry presentation.  It does **not** prove that all level-`n`
swap multiplication identities have van Kampen area bounded independently of
`n`.  Indeed, the authors report that a direct derivation of the infinite
transposition presentation became overly long.  Abstract conjugacy of support
configurations is not yet a quantitative normalized-HS theorem: two
conjugator words naming the same deep swap can differ by a stabilizer word,
and those stabilizer gauges must be synchronized.

## 2. Coherent alternating-packet synchronization (CAP)

Fix the above finite presentation `V=<X|R>`, put

```text
def_R(U)=max_(r in R)||r(U)-I||_2,
```

and let `a=(00 01)`.  For `n>=3`, let `N=2^n`, identify the `N` length-`n`
cylinders with `[N]`, and denote by `a_N in S_N` the induced permutation.
It is a product of `N/4=2^(n-2)` transpositions, hence `a_N in A_N`.

The open CAP statement is that there are universal constants `C,delta_0>0`
such that, for every matrix tuple `U` with `def_R(U)<=delta_0` and every
`n>=3`, one can construct a map

```text
Phi_(n,U):S_N -> U(d)
```

in the **same matrix dimension** as `U`, satisfying

```text
Phi_(n,U)(1)=I,
max_(g,h in S_N)||Phi_(n,U)(gh)-Phi_(n,U)(g)Phi_(n,U)(h)||_2
    <= C def_R(U),                                      (CAP1)
||Phi_(n,U)(a_N)-U(a)||_2 <= C def_R(U).                (CAP2)
```

The essential content is uniformity in `n`.  Gowers--Hatami gives universal
stability only after an all-pairs map such as `(CAP1)` is available; ordinary
normal-form telescoping from a finite presentation has an area cost growing
with `N` and does not prove CAP.

## 3. Complete transposition-complex attack

A concrete way to attack CAP is to keep redundant names rather than choose
one long normal form for every deep swap.

* vertices are the `N` leaf labels;
* a swap variable is attached to every two-subset of leaves;
* overlap/conjugacy cells live on triples of leaves;
* R4/R5-type disjointness and collision cells live on four-subsets;
* R3 identifies the coarse split product with the original word `U(a)`.

The edge graph is the Johnson graph `J(N,2)`, whose normalized spectral gap is
uniform.  The complete simplex also has uniform linear cohomological filling.
These facts suggest a two-stage proof: synchronize the infinitesimal gauges by
a normalized Hodge estimate, then lift the synchronized data nonlinearly in
normalized HS norm.  Neither the nonlinear lifting nor the derivation of all
required triangle/four-cell energies from boundedly many conjugates of
R1--R5 has yet been proved.

The fastest falsification experiment is therefore finite and sparse.  Build
the depth-`n` occurrence/section complex whose vertices are all contextual
names of a level-`n` swap, whose cells are the R1--R5 prototype relations, and
whose comparison edges identify names intended to represent the same swap.
Linearize the gauge equations at the coherent packet and compute the smallest
nonzero singular value of the normalized boundary/Jacobian `D_n`.  A uniform
positive lower bound is necessary for this CAP compiler.  Decay to zero would
kill it before any nonlinear proof is attempted.  A positive linear gap would
still leave the nonabelian lifting problem open.

### A more local S4-chart formulation

There is a sharper finite check which may avoid global van Kampen areas.
Place one exact-model `S_4` chart on every four-subset of the `N` leaves.
Two adjacent charts are contained in a common five-set.  The first symbolic
question is whether, after one common conjugation, every comparison of a swap
name shared by those two charts reduces to one of finitely many depth-three
identities generated by R2, R4, and R5.  A positive answer would make every
local chart-overlap test cost only `O(def_R(U))`, independently of `N`.

For a fixed leaf edge `{i,j}`, its chart contexts are indexed by the
two-subsets of the remaining `N-2` leaves.  Adjacency through a common
five-set is the Johnson graph `J(N-2,2)`, whose normalized spectral gap is
bounded below uniformly in `N`.  A Hilbert-space Poincare estimate can then
synchronize the different contextual copies of that one edge in averaged
squared HS distance.  Doing this for every edge would produce global swap
candidates `T_ij`.

Two qualifications are essential.  First, the finite five-leaf reduction to
R2/R4/R5 has not been checked.  Second, expander synchronization initially
gives an averaged chart estimate, whereas CAP asks for a marked comparison
and an all-pairs multiplication bound.  Polar rounding, compatibility among
the edge averages, and the upgrade from average cell energy to the all-pairs
map required by Gowers--Hatami are part of the open nonlinear step.  This
formulation nevertheless reduces the first possible proof advance to a
finite symbolic audit plus one explicit Johnson-graph estimate.

## 4. Complete conditional collapse

Assume CAP.  Given a `delta`-model `U` in dimension `d`, choose a power of two
`N=2^n` after seeing `d`, so large that

```text
N-1 > d/(1-4(C delta)^2).
```

For `C delta<1/16`, Gowers--Hatami exactifies `Phi_(n,U)` to a representation
`rho:S_N->U(m)` on a flexible enlargement with

```text
d <= m <= d/(1-4(C delta)^2)
```

and with `Phi_(n,U)(g)` uniformly `42 C delta`-close to the compression of
`rho(g)`.  For `N>=7`, every nontrivial complex representation of `A_N` has
dimension at least `N-1`.  Hence `rho|_(A_N)` is trivial.  Since `a_N` is even,
`rho(a_N)=I`, and therefore

```text
||U(a)-I||_2 <= 43 C delta.                             (CAP3)
```

Taking `delta` small proves a strict one-word ceiling, in fact collapse to
zero as the presentation defect tends to zero.  Canonical regular-character
microstates would instead satisfy

```text
||U(a)-I||_2^2 -> 2,
```

so CAP implies that `V` is nonhyperlinear.  The Dudko--Medynets character
classification strengthens the conclusion: the Connes-embeddable support of
the positive word `(1-a)^*(1-a)` is binary, so any strict ceiling below `2`
already collapses the entire nontrivial CE trace face.

## 4A. Preferred weakening: a coherent Carmichael star

The full multiplication table is unnecessary.  Carmichael's presentation is

```text
A_(M+2)=<x_1,...,x_M | x_i^3=(x_i x_j)^2=1, i!=j>,
```

with `x_i=(i,M+1,M+2)` up to permutation convention.  Let
`b=(01 10 11)`, the order-three Bleak--Quick generator.  It is enough to
construct, for every posthoc `M`, matrices

```text
X_i=W_i U(b)W_i^*,
||X_i^3-I||_2 <= C delta,
||(X_iX_j)^2-I||_2 <= C delta             (i!=j),        (CCF1)
```

with one constant independent of `M,d`.

Existence inside the exact group is elementary.  A maximal prefix code with
`M+2` leaves gives a finite subgroup `S_(M+2)<V`; the cycles
`(p_i p_(M+1) p_(M+2))` form the Carmichael family.  They are all conjugate in
`V` to `b`, after refining prefix partitions so that the three moved clopen
pieces and the nonempty fixed complement align.  The problem is quantitative
word coherence in the fixed finite presentation, not existence in `V`.

Indeed, in fixed dimension choose `M` beyond a sufficiently fine finite net
of `U(d)`.  Some `X_i,X_j` are arbitrarily close.  Then `X_iX_j` is close to
`X_i^2`, so `(X_iX_j)^2` is close to `X_i^4`.  Combining `X_i^4 close I` with
`X_i^3 close I` gives

```text
||X_i-I||_2 <= 2C delta+o(1).
```

All `X_i` are exact conjugates of `U(b)`, and the net radius can tend to zero;
therefore

```text
||U(b)-I||_2 <= 2C delta.                                (CCF2)
```

This argument needs no Gowers--Hatami theorem, no flexible enlargement, no
minimal representation degree, and no dimension estimate.  The new open
problem is only to build the Carmichael star from R1--R5 with bounded
normalized-HS cost.  Geometrically one chooses common-pivot three-cycles on
many clopen pieces.  Each is a conjugate of `b`; R4/R5 are the candidate
constant-cost pair-collision cells.  The unresolved issue is again global
word coherence: contextwise Carmichael relations with private gauges are
compatible with the affine-clone firewall.

There is a precise double-coset version of the open word problem.  In the R1
copy of `S_4`, let `a=(00 01)`.  The cycles `b` and `b^a` share two points and
obey `(b b^a)^2=1`.  If one can choose words `g_i` so every relative word
`g_i^(-1)g_j` has a uniformly certified factorization in

```text
C_V(b) a C_V(b^a),
```

with both centralizer certificates literal bounded-use conjugates of the
R4/R5 disjoint-support cells, then `X_i=U(b)^(U(g_i))` satisfy `(CCF1)` with a
universal constant.  This formulation isolates the desired object as an
arbitrarily large certified clique in one orbital double-coset graph.  The
existing literal-orbital block-clique theorem concerns a different affine
lamp-kernel graph and does not supply these Thompson word certificates.

The common-pivot geometry admits an exact smaller reduction.  Fix shallow
leaves `p,q,c_0,c_1`, put

```text
b_0=(p q c_0),       b_1=(p q c_1),       k_1=(c_0 c_1),
```

and for distinct further leaves `c_i,c_j` put

```text
k_i=(c_0 c_i),       k_j=(c_0 c_j),
l_(ij)=(c_0 c_i)(c_1 c_j).
```

Direct permutation multiplication gives

```text
k_i^(-1)l_(ij)=(c_1 c_j),
k_j^(-1)l_(ij)k_1=(c_1 c_i c_j).                       (CF1)
```

Both corrections fix `p,q,c_0`, hence centralize `b_0`.  Therefore the
globally named cycles `u_i=k_i b_0 k_i^(-1)` and
`u_j=k_j b_0 k_j^(-1)` can be moved into the common frame `l_(ij)` by
certifying only the two disjoint-support loops

```text
[b_0,(c_1 c_j)]=1,
[b_0,(c_1 c_i c_j)]=1.                                 (CF2)
```

If both loops have R1--R5 area at most `C`, replacing the four occurrences
in `(u_i u_j)^2` costs at most `4C`.  The remaining loop is a conjugate of
the fixed local-S4 consequence `(b_0b_1)^2`; writing its fixed area as `A_0`
gives

```text
Area_R((u_i u_j)^2)<=4C+A_0.                            (CF3)
```

Thus the finite permutation algebra is constant-cost.  The exact remaining
question is the uniform address-coherence statement in `(CF2)`, recorded as
`thompson-v-r5-uniform-common-pivot-centralizers`.  That proposed subtarget is
now refuted by `finite-mark-centralizer-commutator-area-is-proper`: the
individual endpoint corrections escape in the marked-subgroup Schreier graph,
so their full R1--R5 filling areas are unbounded.  Only a collective or
averaged cancellation mechanism can survive this obstruction.

Bleak--Quick's proof establishes the required swap relations through depth
three and then verifies a fixed Cannon--Floyd--Parry presentation.  It proves
that every loop in `(CF2)` is null, but does not give a bound uniform in the
addresses.  Iterating the displayed R2 transport and R3 split derivations
charges their number of steps.  The necessary negative result is now supplied
by `finite-mark-centralizer-commutator-area-is-proper`: a twisted Schreier
coefficient bounds the area below by centralizer-coset distance, independently
of which R1--R5 cells a diagram uses.

Even that negative direction has a firewall.  Thompson `V` is integrally
acyclic, so `H_1(V,Z)=H_2(V,Z)=0` and every central extension by a trivial
abelian coefficient group splits.  Hence no conjugation-invariant scalar
phase or signed R5-cell count can provide the desired depth lower bound.  A
successful obstruction therefore needs nontrivial module coefficients or a
nonabelian corridor invariant.  The new theorem uses precisely the first
option: Galois-conjugate local coefficients induced from the finite marked
subgroup.

There is also a rigorous limit on this double-coset plan.  In the free group
on the Bleak--Quick generators, conjugates of the free generator `b` act on
disjoint oriented translates of the `b`-axis.  If every edge word
`(b^(g_i)b^(g_j))^2` were literally a conjugate of one word from a fixed
finite template list, all pairwise oriented-axis configurations would have
bounded tree length.  Two anchor axes then confine every other axis to a
fixed finite neighborhood in the locally finite Cayley tree, so the clique
has uniformly bounded size.  Therefore the unbounded Carmichael star cannot
be obtained by one literal R1/R5 conjugate per edge.  Any successful uniform
area proof must use at least a genuinely interacting finite diagram whose
long conjugator boundaries cancel, rather than independent renamed cells.

## 5. Firewalls and nonduplication

This proposal is not the generic one-word ceiling itself.  CAP is a concrete
finite-packet compiler sufficient to prove that ceiling.  It is also not a
restatement of Gowers--Hatami: CAP constructs the all-pairs map to which that
theorem applies.

Pure prefix refinement cannot prove CAP.  The affine-clone model realizes
every finite binary split, conjugacy, commuting-child, and leaf-permutation
pattern exactly in a locally finite group while the root involution retains
squared regular HS energy `2`.  The proposed mechanism must therefore use the
global coherence generated by the exact Bleak--Quick overlap/collision cells,
especially R5; context-local copies of those cells with private conjugator
gauges are still insufficient.

Nor can simplicity, fragmentation, or amenability arguments alone supply the
gap.  Existing simple amenable LEF/sofic firewalls show that qualitative
finite-model failure is not a Connes-embeddability obstruction.  CAP is
specifically a dimension-free normalized-HS synchronization statement for
the fixed Thompson presentation.
