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

## Updated compact counterexample corridor

Seth--Vilalta now supplies the formerly missing purity input in the
`S^6` clutching lane: `C(S^6,D)` is pure for every simple pure `D`, including
`D=C*_r(F_2)`.  The only remaining input in that lane is genuinely unstable
homotopy: a coefficient `D` and a class in a finite unitary group that
survives scalar extension to `D` but dies after extension to `D tensor Z`.
The circle theorem rules out dimension one for this mechanism.

## Exact remaining universal hinge

For a pure `A`, abstract absorption gives

```text
Cu(A) ~= Cu(A) tensor_Cu Cu(Z).
```

The unresolved universal step is still invertibility of the **external**
product morphism from this abstract tensor product to
`Cu(A tensor_min Z)`.  The new results narrow where it can fail: not on
ideals, quotients of a regular ambient algebra, ideal lattices, K-theory,
quasitraces, interval fields, or circle fields with simple stably finite pure
fiber.  What remains is higher-dimensional compact clutching or genuinely
noncompact extension gluing/rank realization.
