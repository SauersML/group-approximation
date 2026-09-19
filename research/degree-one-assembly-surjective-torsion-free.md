---
rg: 2
id: degree-one-assembly-surjective-torsion-free
kind: claim
title: Degree-one assembly is surjective for every torsion-free group
distinct_from:
  whitehead-vanishing-torsion-free: that is the vanishing of a quotient of K_1(ZG); this is surjectivity of a map into K_1(ZG). They are equivalent, by whitehead-is-degree-one-assembly-cokernel, but this is the form in which the literature actually proves cases, so the two are worth carrying separately.
  whitehead-is-degree-one-assembly-cokernel: that claim identifies the cokernel of this map for *every* group and is established; this claim asserts that the map is onto for torsion-free groups and is open. One computes an invariant, the other conjectures its vanishing.
  torsion-free-countable-non-mf: that asks for a torsion-free group failing an operator-algebraic approximation property; this asserts surjectivity of an algebraic K-theory assembly map for all torsion-free groups. Only the words "torsion-free" are shared -- see whitehead-vanishing-torsion-free on why neither property bears on the other.
  torsion-free-finitely-presented-non-mf: that is this program's root about non-MF groups; this is an algebraic K-theory statement quantified over all torsion-free groups, with no approximation content and no finite-presentation hypothesis.
  torsion-free-higman-embedding: that embeds recursively presented torsion-free groups into finitely presented ones and is pure combinatorial group theory; this is a surjectivity statement about assembly maps in algebraic K-theory.
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

For every torsion-free group `G` the degree-one assembly map

    A_1^G : H_1(BG; K(Z)) -> K_1(ZG)

is surjective.

This is equivalent to [[whitehead-vanishing-torsion-free]] by
[[whitehead-is-degree-one-assembly-cokernel]]. It is implied by the
K-theoretic Farrell--Jones conjecture and is therefore known for Lueck's
Farrell--Jones class, including hyperbolic groups, finite-dimensional
CAT(0)-groups, lattices in virtually connected Lie groups, fundamental
groups of manifolds of dimension at most three, and S-arithmetic groups
(arXiv:2507.11337, read at survey level).

The class-wide problem now has an exact finite tester.
[[degree-one-assembly-single-fp-tester-equivalence]] constructs one finitely
presented torsion-free group `U` for which

```text
A_1^U is onto
    <=>
A_1^G is onto for every torsion-free G.
```

Thus the unresolved input is the single computation
[[degree-one-assembly-surjective-universal-tester]].

## Colimits are not the obstruction

The previous version of this node incorrectly said that degree-one
surjectivity fails to pass through directed colimits. It does pass:
`H_1(BG;K(Z))=C_2 direct-sum G_ab`, group abelianization, group rings,
and algebraic `K_1` all commute with filtered colimits. The assembly maps
are compatible, and filtered colimits of surjective homomorphisms are
surjective. Equivalently, ordinary Whitehead groups commute with filtered
colimits.

The genuine obstruction to the classical universal-group shortcut was
subgroup inheritance. From an arbitrary embedding `H<=U`, vanishing of
`Wh(U)` need not imply vanishing of `Wh(H)`. The new construction repairs
exactly that step by making every induced map `Wh(H)->Wh(U)` injective for
the recursively presented support groups needed by the global reduction.

The statement remains **OPEN**. The reduction changes its quantifier shape
from a proper class of groups to one finite presentation; it does not compute
that presentation's assembly map.
