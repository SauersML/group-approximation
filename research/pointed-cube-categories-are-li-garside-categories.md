---
rg: 2
id: pointed-cube-categories-are-li-garside-categories
kind: claim
title: The pointed-cube category of every free cocompact cubulation, special or not, is a Garside category in Li's sense with solvable word problem for its full groups; the naive power without a grading (hyperplane count mod M) destroys disjoint mcms
distinct_from:
  raag-cube-codings-fail-li-multiplicity-at-every-power: that shows Li's (t<d) fails for RAAG (special) codings at every power; this proves the Garside layer for all cubulations including non-special ones, and kills the grading-free power.
  commutative-cube-degree-maps-force-tree-products: that shows commutative (UFP*) gradings force tree products; this covers the remaining naive power, the non-(UFP*) count subcategory.
---

**ESTABLISHED** through `pointed-cube-categories-li-garside-proof` (lane proof,
elementary apart from standard CAT(0) cube complex facts; X. Li, arXiv:2110.04505v2, read
at source; not independently reviewed; no priority claimed).

**Setting.** `X` is a locally finite, finite-dimensional CAT(0) cube complex and `G`
acts on `X` freely on vertices and cocompactly. **No specialness is assumed**: hyperplane
orbits may self-cross or inter-osculate, so no hyperplane colouring gives a trace-monoid
degree map. `C_X` is the pointed-cube category of
`cubulated-groups-act-by-bisections-of-a-pointed-cube-category`, and `S` is its set of cube
morphisms.

**1. Garside layer, for all cubulations.** `C_X` satisfies every standing hypothesis of
Li's Theorem `intro:Gars`:
- finitely many objects;
- left and right cancellative, with trivial units, so condition (F) holds;
- finitely aligned with disjoint mcms: two morphisms have at most one lcm, the median
  join;
- right Noetherian.

`S` is a locally finite, `=^*`-transverse Garside family whose normal forms are the
Niblo--Reeves normal cube paths. Each `(S^{≤L})^♯` is closed under left divisors, being
the morphisms whose hyperplane poset has height at most `L`.

Consequences:
- For every closed invariant `X_0 ⊆ Ω_∞` and base cylinder `Y`, the topological full group
  `F((I_l ⋉ X_0)_Y^Y)` is an isotropy group of the enveloping groupoid of a Garside category.
- `F(I_l ⋉ ∂Ω)` has solvable word problem, by Li's Corollary `intro:WordProblem`.

In particular Li's Garside machinery does **not** need the trace-monoid degree map that
exists only in the special case (Attempt 1 of the parent). Non-special cubulated groups
enter it exactly as special ones do.

**2. Finiteness layer: the same obstruction for special and non-special.**
- **(`t < d`) fails already on a RAAG.** It fails at every power for
  `raag-cube-codings-fail-li-multiplicity-at-every-power`, including the `F_2` tree. The
  Garside family `S^{≤M}` is not a power operation.
- **Commutative gradings force tree products.** By
  `commutative-cube-degree-maps-force-tree-products`, (UFP*) gradings into a commutative
  monoid, which would supply powers, exist only for products of trees.
- **The grading-free power fails too.** Take the subcategory of morphisms whose hyperplane
  count is divisible by `M`. It has the same boundary as `C_X` up to a `Z/M` phase, but it
  loses disjoint mcms already for `Z²` with `M = 2`. So Li's `intro:Gars` does not
  apply to it.

So for every cubulation that is not a product of trees, whether it is special or has
self-crossing hyperplanes, the binding gate is the same: **a power operation for an
ungraded Garside category**. That means a category with the same boundary groupoid, up
to finite-index phase, that keeps disjoint mcms and satisfies (`t < d`). A finiteness
certificate for `F((I_l ⋉ X_0)_Y^Y)` that bypasses (`t < d`) would also do.

## Lesson for general BH

The Garside layer comes free for any group with a finite-state geodesic combing whose
prefix order has conditional joins (median joins, here), so all cubulated groups have it,
with no specialness needed. It gives normal forms, the word problem and Li's category of
bisections.

What is missing everywhere beyond products of trees is a power operation. The obvious
ones fail in two ways:
- gradings with unique factorization force product structure;
- counting modulo `M` destroys disjoint mcms.

So the new tool needed for higher-rank Boone--Higman hosts is a way to make every basic
piece reappear twice in its own expansion when "time" is a poset, not a product of chains.
Non-special cube complexes add nothing to this obstruction.
