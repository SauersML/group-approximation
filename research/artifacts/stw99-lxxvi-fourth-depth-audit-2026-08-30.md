# STW LXXVI fourth-depth audit: locality, shadows, and circle clutching

## Exact definition and current literature boundary

STW Definition 24 calls a **separable** C*-algebra `A` Cuntz semigroup
regular when the particular first-factor embedding

```text
A -> A tensor_min Z,       a |-> a tensor 1_Z
```

induces an isomorphism on `Cu`.  An abstract isomorphism between the source
and target semigroups is not the definition.  Problem LXXVI asks whether
this follows from almost unperforation and almost divisibility of `Cu(A)`.

The primary-literature screen through 2026-08-30 found no general solution.
The closest current structural inputs are:

- Antoine--Perera--Thiel,
  [Tensor products and regularity properties of Cuntz semigroups](https://arxiv.org/abs/1410.0483),
  for abstract `Cu(Z)` absorption;
- Ciuperca--Robert--Santiago,
  [Cuntz semigroups of ideals and quotients](https://arxiv.org/abs/0710.5800),
  for exactness of `Cu`;
- Perera--Thiel--Vilalta,
  [Extensions of pure C*-algebras](https://arxiv.org/abs/2506.10529),
  proving that pureness is equivalent to pureness of an ideal and quotient;
- Seth--Vilalta,
  [Continuous functions over a pure C*-algebra](https://arxiv.org/abs/2602.14809),
  proving in particular that `C(X,D)` is pure for compact metric `X` and
  simple pure `D`; and
- Antoine--Dadarlat--Perera--Santiago,
  [Recovering the Elliott invariant from the Cuntz semigroup](https://arxiv.org/abs/1109.5803),
  for the interval and circle `Cu` calculations used below.

The 2026 central-purity theorem characterizes Z-stability through purity of
central sequence algebras; it does not identify the external Cu tensor map
for an arbitrary pure algebra, so it does not settle LXXVI.

## New locality theorem

Cu-regularity passes to ideals and quotients.  On an ideal this is a direct
support calculation: if `[a tensor 1_Z]` lies in `Cu(I tensor Z)`, a slice
map puts `a` in `I`.  On a quotient, exactness identifies the two quotient
Cu-semigroups, and the ideal restriction lets the ambient isomorphism
descend.  Full-hereditary Morita invariance then gives permanence for all
hereditary subalgebras.

This is asymmetric with the new purity extension theorem.  Pureness is
equivalent to pureness of an ideal and quotient, but the converse extension
step for **Cu-regularity** remains unavailable.  Thus a universal proof must
control how two regular Cu pieces glue; checking every ideal and quotient
separately is insufficient with current methods.

## All coarse shadows agree automatically

For every separable `A`, the first-factor embedding already preserves the
entire ideal lattice, both K-groups, and the quasitrace cone.  These follow,
respectively, from the ideal theorem for tensoring by the simple nuclear
algebra `Z`, the KK-equivalence `C->Z`, and STW Lemma 22(i).

Consequently a counterexample must be invisible to all three shadows.  The
finite compact corridor is cancellation or clutching at fixed local K0; the
soft corridor is failure of rank realization or noncompact gluing at fixed
ideal and quasitracial data.

## New circle permanence and pure-field theorem

The reusable theorem needs less than purity.  If `D` is simple, separable,
stable rank one, and Cu-regular, then `C(T,D)` is Cu-regular.  A projection
over `C(T,D)` is a projective-module bundle
obtained by clutching a fixed fiber module around the circle.  Stable rank
one does two jobs:

1. it cancels the fiber projection; and
2. in every full fiber corner it identifies connected components of
   unitaries injectively with `K_1`.

Therefore a stable equivalence of two circle bundles cancels both their
fiber and clutching data.  Projections over `C(T,D)` cancel.

The circle Cu formula then separates into

```text
V(C(T,D)) disjointUnion Lsc_nc(T,Cu(D)).
```

The compact term is `{0} disjointUnion V(D)^* times K_1(D)` and is preserved
by the `V` and `K_1` isomorphisms for `D->D tensor Z`.  The noncompact term
is preserved pointwise by the assumed fiber Cu isomorphism.  Hence
`C(T,D)` is Cu-regular.  For a simple separable stably finite pure `D`, Lin
supplies stable rank one and STW Proposition 23 supplies fiber Cu-regularity,
giving the stated Problem LXXVI positive class.

Taking `D=C*_r(F_2)` gives a non-simple exact nonnuclear circle field that is
Cu-regular but not Z-stable.  This also shows that circle monodromy itself is
not a counterexample mechanism.

## New one-dimensional theorem at the exact K1-free boundary

The available one-dimensional Cu formulas have different hypotheses, and
they must not be conflated.  Antoine--Dadarlat--Perera--Santiago, Theorem 2.6,
computes the interval for a simple separable stable-rank-one coefficient with
no `K_1` restriction.  Their Theorem 3.7 treats the circle with arbitrary
`K_1` by separating the projection-clutching summand.  In contrast,
Antoine--Perera--Santiago, Theorem 3.4, gives the pointwise formula over every
second-countable one-dimensional locally compact space under the stronger
coefficient hypothesis

```text
stable_rank(B)=1,
K_1(I)=0 for every closed two-sided ideal I of B.          (1D1)
```

The formula itself gives a reusable permanence theorem on its full published
base class.  Let `X` be any second-countable locally compact Hausdorff space
of covering dimension at most one, and put `E=B tensor Z`.  If both `B` and
`E` have stable rank one and satisfy `(1D1)`, and the actual map
`Cu(B)->Cu(E)` is an isomorphism, then the formula applies to both
coefficients.  Under the two natural evaluation identifications, the
first-factor Cu map is pointwise application of the coefficient map.  It is
therefore an isomorphism:

```text
Cu(C_0(X,B)) -> Cu(C_0(X,B) tensor Z).
```

For a simple coefficient, `(1D1)` reduces to stable rank one and `K_1(B)=0`.
Thus if `D` is simple, separable, stably finite, pure, and `K_1(D)=0`, Lin
gives stable rank one for `D` and `D tensor Z`, the KK-equivalence
`D->D tensor Z` preserves zero `K_1`, and STW Proposition 23 gives the fiber
Cu isomorphism.  Hence `C_0(X,D)` is Cu-regular.  It is also pure: apply
Seth--Vilalta to `C(X^+,D)`, where `X^+` is the compact metrizable one-point
compactification, and use permanence of purity for its ideal `C_0(X,D)`.
This strictly subsumes the finite-graph statement: the base may be
noncompact, have infinite branching, or contain infinitely many cycles.

The `K_1` restriction is a trust boundary of this proof, not cosmetic.
Antoine--Dadarlat--Perera--Santiago, Remark 3.9, attach an interval to a circle
and show that pointwise comparison can miss a nontrivial clutching class when
the simple stable-rank-one coefficient has nonzero `K_1`.  Thus neither the
pointwise formula nor the new Cu-regularity theorem is asserted after deleting
the idealwise `K_1` hypothesis.

## Updated compact counterexample corridor

Seth--Vilalta now supplies the formerly missing purity input in the
`S^6` clutching lane: `C(S^6,D)` is pure for every simple pure `D`.
Jiang's weak homotopy equivalence between all matrix unitary groups of a
Z-stable algebra supplies a second simplification.  Every scalar class that
is stably zero automatically dies after passing to `D tensor Z`; this applies
to `alpha in pi_5(U(2))=Z/2`.  Thus the lane needs only survival before Z.

There is also a new exclusion.  A unital copy of `Z` inside `D` factors the
scalar map through a K-stable unitary group, so it kills `alpha` already in
`U(M_2(D))`.  Thiel--Winter prove that `Z` embeds unitally in
`C*_r(F_2)`.  Hence the natural free-group coefficient is not merely
uncomputed: it cannot be the witness.  Any successful coefficient must be
simple, pure, and admit no unital embedding of `Z`.  The circle theorem rules
out dimension one for this mechanism as well.

There is an independent finite-dimensional no-go.  If `M_k` embeds unitally
in `D` for `k>=2`, the scalar map on unitary groups factors through

```text
U(2) -> U(2k),                 u |-> u tensor 1_k.
```

After a fixed permutation conjugacy this is the `k`-fold block sum.  Its
stable image on `alpha in pi_5(U(2))=Z/2` is zero because
`pi_5(U)=Z` is torsion free.  The fibration
`U(n)->U(n+1)->S^(2n+1)` shows that stabilization is an isomorphism on
`pi_j` for `j<2n`; since `5<4k`, `pi_5(U(2k))->pi_5(U)` is injective.
Therefore the tensor-amplified class is already zero in `U(2k)`, and hence
in `U(M_2(D))`.  Any surviving coefficient must contain no unital matrix
subalgebra of size at least two.  This conclusion uses the exact finite
stable range and does not confuse tensor amplification with ordinary corner
stabilization.

The same calculation has a projectionless finite-divisibility extension.
For `p,q>=2`, the unitary group of the generalized dimension-drop block at
matrix level two is the homotopy pullback

```text
U(2p) times^h_(U(2pq)) U(2q).
```

The scalar `alpha` dies at both endpoints by the matrix-amplification
theorem.  The homotopy-pullback exact sequence says that any remaining class
comes from `pi_6(U(2pq))`.  This group is already stable because `6<4pq`,
and Bott periodicity makes it zero.  Hence one unital `I_(p,q)` inside a
coefficient kills `alpha` before Z-stabilization.

For coprime `p,q`, `I_(p,q)` has only zero and the unit as projections: the
constant rank of a projection must be divisible by both endpoint sizes.
It therefore contains no unital matrix algebra of size at least two; as a
subhomogeneous algebra it also cannot contain the simple infinite-dimensional
algebra `Z`.  The new no-go is strictly weaker than both previous embedding
hypotheses.  It does not prove that purity supplies such a block, but forces
any surviving pure coefficient to fail even this finite dimension-drop
divisibility test.

The homotopy-pullback argument extends to every unital one-dimensional NCCW
block.  Write the zero-skeleton and one-cell algebra as

```text
E=directSum_i M_(r_i),              F=directSum_j M_(d_j),
```

with unital endpoint multiplicity matrices `mu_0,mu_1`.  Evaluation onto
`E` sends the scalar class to the tuple of amplifications
`alpha->pi_5(U(2r_i))`.  If some `r_i=1`, that tuple retains the original
nonzero `alpha`, so the class cannot die in the pullback.

If every `r_i>=2`, every tuple component vanishes by finite stable range.
The homotopy-equalizer exact sequence then leaves only a possible image from

```text
pi_6(U(M_2(F)))=directSum_j pi_6(U(2d_j)).
```

Unitality gives `d_j=sum_i m_(epsilon,j,i)r_i>=2`; hence every summand is in
the stable range and is zero by `pi_6(U)=0`.  Therefore the scalar class dies.
The exact criterion is simply

```text
min_i r_i>=2.
```

All numerical endpoint multiplicities otherwise disappear: if there is a
scalar vertex, evaluation detects it before the endpoint maps act; if there
is none, the entire residual obstruction group vanishes.  Thus any surviving
coefficient must exclude every unital one-dimensional NCCW block with
character-free zero-skeleton, not only prime dimension-drop blocks.

## Exact remaining universal hinge

For a pure `A`, abstract absorption gives

```text
Cu(A) ~= Cu(A) tensor_Cu Cu(Z).
```

The unresolved universal step is still invertibility of the **external**
product morphism from this abstract tensor product to
`Cu(A tensor_min Z)`.  The new results narrow where it can fail: not on
ideals, quotients of a regular ambient algebra, ideal lattices, K-theory,
quasitraces, interval fields, circle fields with simple stably finite pure
fiber, or fields over any second-countable locally compact one-dimensional
base whose such fiber has trivial `K_1`.  What remains is higher-dimensional
compact clutching over a pure coefficient with no unital `Z`, supportwise
one-dimensional clutching for nonzero-`K_1` fibers, or genuinely noncompact
extension gluing/rank realization.
