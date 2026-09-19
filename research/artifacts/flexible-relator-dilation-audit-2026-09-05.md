# Exact low-rank curvature does not imply flexible unitary repair

There are explicit permutation tuples for the one-relator group

```text
G=BS(2,3)=<a,t | t a^2 t^(-1)=a^3>
```

whose defining error is **exactly supported** on a vanishing-rank
subspace, yet every exact finite-dimensional unitary representation,
even after sublinear dimension padding, stays a fixed distance away.
Thus factoring each relator error through a small space is insufficient
for a universal unitary-dilation repair theorem.

This does not disprove a repair theorem assuming vanishing of `H^2` for
all unitary Hilbert coefficients. The same group has an explicit unitary
coefficient module with nonzero, even reduced, `H^2`. The final section
constructs it and identifies the precise resonance missed by the apparent
two-versus-three scalar gap.

All constructions below are analytical; no permutations were enumerated
and no computation or build was run.

## 1. An explicit sequence of permutations

Fix `n>=3`, put `Q=6^n`, and use `n+1` disjoint sets `H_0,...,H_n`,
each containing `Q` points. The total matrix dimension is
`d=(n+1)Q`. Set

```text
L_k=2^k 3^(n-k)       (0<=k<=n).
```

Choose a permutation `A_k` of `H_k` all of whose cycles have length
`L_k`, and let `A` be their disjoint union. We next choose permutations
`B_k` on `H_k`, for `k<n`, such that

```text
B_k^2=A_k^3,
every cycle of B_k has length L_(k+1)=2L_k/3.            (FRD1)
```

For any `k<n`, this is possible: `A_k^3` has
`3Q/L_k=2^(n-k)3^(k+1)` cycles of length `L_k/3`, and their number is
even. Pair those cycles and interleave each pair. Squaring the resulting
cycle of length `2L_k/3` recovers the original pair.

On the interior levels `1<=k<=n-2`, make a more specific choice which
also forces noncommutation. Put `L=L_k/3` and consider

```text
F_k=(Z/(6L)Z) times S_3,
alpha=(2,c),     beta=(3,tau),
```

where `c` is a three-cycle and `tau` is a transposition. Then

```text
alpha^3=(6,1)=beta^2,
order(alpha)=3L=L_k,
order(beta)=2L=L_(k+1),
[beta,alpha]=(0,[tau,c]) != 1.                         (FRD2)
```

The group has order `36L=12L_k`. The quotient

```text
Q/(12L_k)=2^(n-k-2)3^(k-1)
```

is an integer for exactly the indicated interior range. On `H_k`, take
this many copies of the left regular permutations of `F_k` and let
`A_k,B_k` be the actions of `alpha,beta`. They have the stipulated cycle
types and satisfy `(FRD1)`. Their commutator has no fixed point, because
it is left translation by a nonidentity group element. On levels `0`
and `n-1`, use the elementary cycle-pairing construction instead.

For each `0<=k<n`, the permutations `A_(k+1)` and `B_k` have identical
cycle types on sets of the same size. Choose a bijection
`T:H_(k+1)->H_k` conjugating the former to the latter. Complete `T`
by any bijection `H_0->H_n`. These block bijections assemble into one
permutation of the entire set. Define `B=TAT^(-1)`. Its restriction to
every `H_k` with `k<n` is precisely the prescribed `B_k`.

## 2. One exactly supported relator and a macroscopic forbidden word

Let

```text
R=T A^2 T^(-1) A^(-3)=B^2 A^(-3),
W=[B,A]=T A T^(-1) A T A^(-1) T^(-1) A^(-1).
```

By `(FRD1)`, `R` is the identity on `H_0,...,H_(n-1)`. If `P_n`
projects onto the last block, then exactly

```text
R-I=P_n(R-I)P_n,
rank(P_n)/d=1/(n+1),
||R-I||_2^2<=2/(n+1).                                  (FRD3)
```

The norm estimate follows from the fixed-point formula for a permutation
matrix: `||R-I||_2^2=2(1-tr_d(R))`. Its rank defect also satisfies
`rank(R-I)/d<=1/(n+1)`.

On the `n-2` interior levels, `(FRD2)` says that `W` has no fixed
point. Hence

```text
0<=tr_d(W)<=3/(n+1),
||W-I||_2^2>=2(n-2)/(n+1) -> 2.                        (FRD4)
```

This is an explicit approximate representation with a single defining
error factoring through a small space. The defining error is not merely
small outside that space: it vanishes there identically.

## 3. Every exact unitary representation kills the forbidden word

Suppose finite-dimensional unitaries `A_0,T_0` satisfy the defining
relation, and put `B_0=T_0 A_0 T_0^*`. Then `B_0^2=A_0^3`.

List the eigenvalues of `A_0`, with multiplicities, as `lambda_i`.
Conjugacy of `A_0^2` and `A_0^3` gives a permutation `sigma` of this
list with `lambda_i^2=lambda_(sigma(i))^3`. Going around any cycle of
length `ell` gives

```text
lambda_i^(2^ell)=lambda_i^(3^ell).
```

Therefore every eigenvalue has finite order coprime to six, and so does
`A_0` itself. Let that order be `q`. The conjugate `B_0` has the same
order. Choose `u` with `2u=1 mod q`. Then

```text
B_0=(B_0^2)^u=A_0^(3u).
```

It follows that `[B_0,A_0]=I` in every exact finite-dimensional unitary
representation. This argument does not use residual-finiteness or a
soficity theorem.

Now pad the tuple `(A,T)` by identities to any dimension `D>=d`.
Let `rho` be any genuine representation on that dimension, with maximum
generator error `e` in normalized HS norm. Word telescoping for the
eight-letter word `W`, whose value at `rho` is the identity, gives

```text
8e >= sqrt(d/D) ||W-I||_(2,d)
    >= sqrt(d/D) sqrt(2(n-2)/(n+1)).                   (FRD5)
```

Consequently, if `D/d->1`,

```text
liminf e >= sqrt(2)/8.
```

Even padding by a bounded dimension factor leaves a positive lower bound.
The estimate is invariant under the chosen unitary identification of the
original subspace with the first summand. A convention allowing deletion
of `o(d)` original dimensions cannot remove the obstruction either:
changing or discarding that many dimensions changes the normalized word
norm by `o(1)`, whereas `(FRD4)` remains macroscopic. Equivalently such a
flexible correction can be converted to the identity-padding convention
with `o(1)` additional generator error.

Thus no simultaneous approximate repair to exact representations with
`d+o(d)` dimension can follow solely from low-rank factorizations of the
defining errors, even for a presentation with one two-cell.

## 4. Extending compressed operators is a different problem

If a unitary on a larger Hilbert space has compression to a subspace
equal to a prescribed unitary on that subspace, the subspace is already
reducing. Indeed the compressed image of every vector has the same norm
as the full image, so the orthogonal output component is zero. The
unitary maps that subspace onto itself, and its orthogonal complement is
invariant as well.

It follows that exact principal-compression dilation of an entire
unitary generator tuple to a genuine representation is possible only
if the original tuple already satisfies every relation. Dilating
nonunitary compressed generators avoids that elementary obstruction,
but it introduces the different requirement that the dilations satisfy
all group relations simultaneously. Equations `(FRD3)`--`(FRD5)` show
that individually small relator-support spaces do not guarantee this
simultaneous extension even approximately in normalized HS norm.

The cellular interpretation is equally limited. The finite presentation
has only one two-cell, and its scalar cellular boundary has nonzero
`a` exponent sum `2-3=-1`. Scalar degree-two cohomology of that
presentation complex vanishes. Yet its matrix-valued defects cannot
be repaired as above. The missing data cannot be supplied by counting
two-cells or their scalar boundaries.

## 5. BS(2,3) does not satisfy all-unitary degree-two vanishing

The possible stronger hypothesis was checked separately. Here is an
explicit unitary module with a nonzero degree-two obstruction.

Let `Lambda` be the countable group of roots of unity whose orders
divide some `6^m`. On a separable Hilbert space, choose a diagonal
unitary `A` with each `lambda in Lambda` occurring with countably
infinite multiplicity. Every element of `Lambda` has both square and
cube roots in `Lambda`. Consequently `A^2` and `A^3` have precisely
the same eigenvalues, each with countably infinite multiplicity.

Choose an eigenvector `w` for `A` with eigenvalue `-1` and an eigenvector
`v` with eigenvalue `omega`, a primitive cube root. There is a permutation
unitary `T` with

```text
T A^2 T^*=A^3,
T w=v.                                                (FRD6)
```

To construct it, for each eigenvalue `xi`, choose a bijection from an
eigenbasis of `A^2` at `xi` to an eigenbasis of `A^3` at `xi`. In the
`xi=1` bijection prescribe the pair `w->v`; both remaining bases are
still countably infinite. Their disjoint union gives `T`. Thus these
operators define a genuine unitary representation of `BS(2,3)`.

The standard presentation complex is a classifying space: it is the
graph of circles with edge maps of degrees two and three. Its universal
cover is the corresponding Bass--Serre tree of contractible lines and
strips, and is contractible. The cellular Hilbert-coefficient cochain
complex therefore computes ordinary group cohomology. Its last
differential is the Fox row

```text
D:H direct_sum H -> H,
D_a=T(I+A)-(I+A+A^2),
D_t=I-A^3,
D(x,y)=D_a x+D_t y.                                   (FRD7)
```

The vector `v` from `(FRD6)` is orthogonal to its image. Indeed,

```text
D_t^*v=(I-A^(-3))v=0,
D_a^*v=(I+A^(-1))T^*v-(I+A^(-1)+A^(-2))v
      =(I+A^(-1))w-(1+omega^(-1)+omega^(-2))v=0.        (FRD8)
```

The first term vanishes at the eigenvalue `-1`; the second vanishes
at the primitive cube root. Since `v!=0`, the range of `D` is not even
dense. Thus both ordinary and reduced `H^2(G,H_pi)` are nonzero for
this representation.

The apparent invertible expression `2T-3I` occurs on a sector where
`A=I`. It does not control the `A=-1` to `A=omega` transition in
`(FRD6)`. This is why the two-versus-three imbalance cannot establish
all-unitary cohomological vanishing for this group.

The endpoint is therefore exact: low-rank relator factorization alone
has a concrete flexible-unitary countermodel, while the arithmetic
all-unitary-`H^2` surgery question survives this test. Any use of that
stronger hypothesis must control the relevant twisted coefficient
modules; scalar cohomology, cell counts, and independent unitary
dilations do not do so.

## 6. Independent audit of the enlarged small-angle Hilbert module

The proposed enlargement of the regular coefficient module is valid.
For a positive scale `delta_j->0`, let `H_small(delta)` be the closure
in the matrix Hilbert ultraproduct of the classes represented by
2-norm-bounded matrices `Y_j` satisfying

```text
delta_j ||Y_j||_op ->_omega 0.
```

Its defining vector space is preserved by arbitrary left and right
unitary sequences. Every individual adjoint operator therefore preserves
the closed space and its orthogonal complement. On a defining vector,
the group-law error is bounded by
`2||Y_j||_op||D_j-I||_2=o(1)` when the word defect is `O(delta_j)`.
Thus the adjoint action is genuine on this larger module too.

For operator-bounded `A_j,B_j` of 2-norm `O(delta_j)`, the scaled
product `A_jB_j/delta_j` is 2-norm bounded and has pairing at most
`O(delta_j||Y_j||_op)` against a defining vector. Its projection onto
`H_small(delta)` is consequently zero. The unitarity and associativity
identities therefore again produce a genuine projected 2-cocycle.

Closure causes no representative gap: a vector in `H_small(delta)`
admits a representative with `delta_j||Y_j||_op->0` after an
ultrafilter diagonal choice from its defining approximants. For such
a skew-Hermitian correction `b_j`,

```text
||exp(delta_j b_j)-I-delta_j b_j||_2/delta_j
 <= (delta_j||b_j||_op)||b_j||_2/2 -> 0.
```

Also `||b_j E_j||_2<=||b_j||_op O(delta_j)=o(1)` for an original
unscaled defect `E_j` of 2-norm `O(delta_j)`. Approximation extends
these estimates across the closed space. These are exactly the nonlinear
estimates needed for projected cohomological correction.

In particular, if every original defining error tends to zero in
operator norm, each rescaled defining error belongs to this module.
All fixed-word rescaled errors do as well. Actual all-unitary `H^2`
vanishing then gives one correction with HS defect `o(delta_j)`.
Moreover the correcting exponentials are operator-norm close to the
identity. Thus operator-small defining defects remain operator-small
after each fixed finite number of these corrections. This statement
still does not give a scale-uniform infinite iteration.

For a 2-norm-bounded class `X=[E_j/delta_j]`, orthogonality to this
larger space is equivalent to

```text
lim_(t down to 0) lim_omega
 ||(E_j/delta_j)1_(|E_j|<=t)||_2=0.                    (FRD9)
```

The forward implication follows by diagonalizing low-angle truncations:
if a positive amount of their 2-mass survived as `t->0`, choose
`t_j->0` slowly enough that the truncated vectors retain it. Those
vectors satisfy `delta_j||Y_j||_op<=t_j` and have nonzero pairing with
`X`. For the converse, pair separately against low and high angles.
The low pairing is bounded by the low-angle 2-norm; on the high-angle
support the rank bound `tr(P)<=O(delta_j^2/t^2)` bounds the pairing by
`O(delta_j||Y_j||_op/t)`, which vanishes for fixed `t`.

There is an important quantifier limitation. For each *fixed* cutoff
`t>0`, the retained hard-angle projection has rank `O(delta_j^2 d_j)`,
with constant depending on `t`. To make its omitted energy `o(delta_j)`,
one may need `t=t_j->0`, losing that uniform rank constant. The following
exact spectral example shows this loss cannot be omitted from `(FRD9)`.

Take `d_j=2^(3j)`. For `1<=k<=j`, give a diagonal unitary exactly
`2^k` eigenvalues with phase `theta_k`, chosen so that
`|exp(i theta_k)-1|=2^(-k)`; put all other eigenvalues equal to one.
Let `E_j` be this unitary minus identity and set

```text
delta_j^2=||E_j||_2^2=(1-2^(-j))/d_j.
```

The normalized squared energy at level `k` tends to `2^(-k)`.
Consequently its low-angle energy satisfies `(FRD9)`, since
`sum_(2^(-k)<=t)2^(-k)<=2t`. Thus `E_j/delta_j` is orthogonal to
`H_small(delta)`.

Fix any finite `C`. A projection with rank at most
`C delta_j^2 d_j` has rank at most `C`. Choose a fixed `k` with
`2^k>C`, and let `R_(j,k)` be the level-`k` spectral projection.
For every such projection `P_j`,

```text
||E_j(I-P_j)||_2^2/delta_j^2
 >= 2^(-2k)(2^k-C)/(1-2^(-j)) > 0                    (FRD10)
```

once `j>=k`. This follows from
`Tr(R_(j,k)P_j)<=rank(P_j)`. Therefore no uniform
`O(delta_j^2 d_j)` rank removal makes the complementary error
`o(delta_j)`, despite `(FRD9)`. The example is a counterexample to that
stronger spectral inference, not to the cohomological construction or
to the possibility of repairing these particular unitaries by another
operation.

The enlarged module is genuine analytic progress: it removes all
small-angle curvature visible at this scale and strictly enlarges the
uniformly integrable sector. Its proved endpoint retains a two-parameter
cutoff ledger. A dilation theorem must respect that ledger or supply
additional structure beyond `(FRD9)`.
