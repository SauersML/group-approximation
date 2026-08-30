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

## New finite-graph theorem at the exact K1-free boundary

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
K_1(I)=0 for every closed two-sided ideal I of B.          (FG1)
```

For a simple coefficient, `(FG1)` reduces to stable rank one and `K_1(B)=0`.
This closes a genuinely larger base-space class without a new pullback claim.
If `X` is any finite graph and `D` is simple, separable, stably finite, pure,
and `K_1(D)=0`, the formula applies to both `D` and `D tensor Z`: Lin gives
stable rank one, and the KK-equivalence `D->D tensor Z` preserves the zero
`K_1` group.  Under the two natural evaluation identifications, the
first-factor Cu map is pointwise application of the fiber map, which is an
isomorphism by STW Proposition 23.  Hence

```text
Cu(C(X,D)) -> Cu(C(X,D) tensor Z)
```

is an isomorphism.  Seth--Vilalta independently makes `C(X,D)` pure.  The
class includes finite trees, bouquets of circles, theta graphs, and arbitrary
finite combinations of branching and cycles.

The `K_1` restriction is a trust boundary of this proof, not cosmetic.
Antoine--Dadarlat--Perera--Santiago, Remark 3.9, attach an interval to a circle
and show that pointwise comparison can miss a nontrivial clutching class when
the simple stable-rank-one coefficient has nonzero `K_1`.  Thus neither the
pointwise formula nor the new Cu-regularity theorem is asserted for arbitrary
fibers over a general finite graph.

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
fiber, or finite-graph fields whose such fiber has trivial `K_1`.  What
remains is higher-dimensional compact clutching over a pure coefficient with
no unital `Z`, supportwise one-dimensional clutching for nonzero-`K_1`
fibers, or genuinely noncompact extension gluing/rank realization.
