---
rg: 2
id: degree-category-full-groups-stabilized-have-type-a-actions
kind: claim
title: If the Cuntz-stabilized full group of a finite degree category with strongly connected pieces is finitely presented, its action on clopen sets has type (A), finite groups of units allowed
distinct_from:
  stabilized-kgraph-full-groups-have-type-a-actions: that is the case of plain k-graphs with two loops of every colour, where Li's theorem supplies finite presentation; this allows finite groups of units, needs no loops outside the Cuntz colour for the comparison, and takes finite presentation as a hypothesis.
  primitive-aperiodic-two-graph-full-groups-embed-in-fp-simple: that produces simple hosts; this produces type (A) actions, hence the permutational class B_A, which is closed under finite-index overgroups.
---

**ESTABLISHED** through `degree-category-comparison-type-a-proof` (lane proof,
elementary; not independently reviewed; no priority claimed).

**Setting.** `ℭ` is a finite left cancellative small category with a degree map
`d : ℭ -> N^k`, as in Li (arXiv:2110.04505, §`s:Gars-deg`). Its invertibles are the
morphisms of degree 0, and for each object they form a finite group. Assume (UFP*):
a morphism of degree `m + m'` factors as one of degree `m` followed by one of degree
`m'`, uniquely up to a unit in between. Assume also that finitely many morphisms of
each degree end at each object, and that from every object there are morphisms of
every degree.

The objects split as `V_1 ⊔ ... ⊔ V_q` into *pieces*: no morphism joins different
pieces, and for `u, w` in one piece some morphism has target `u` and source `w`.
Let `𝒢` be Li's boundary groupoid `I_l ⋉ ∂Ω` and `Z` the union of the boundaries of
a set of objects. Let `𝒢'' = 𝒢|_Z x 𝒢_(O_2)` on `C'' = Z x {0,1}^N`, the groupoid of
`ℭ x O_2` (its degree takes values in `N^(k+1)`).

**Statement.** Suppose `D = F(𝒢'')` is finitely presented. Then:
1. any two nonempty clopen subsets of the same piece `C''_s` of `C''` are equivalent
   by a compact open bisection;
2. the action of `D` on the nonempty proper clopen subsets of `C''` is of type (A);
3. `D`, `F(𝒢|_Z)` (through `g ↦ g x id`) and all their subgroups lie in `B_A`.

**When finite presentation holds.** Li's Theorem `thm:deg` gives type `F_∞` when every
object has at least two loops of every colour and condition (F) holds, for example
when `ℭ` is right cancellative (Li, l.1456). Rescaling degrees by a multiple of the
periods supplies the loops, as in `tree-lattice-kgraph-power-phase-proof` and
`primitive-two-graph-fp-simple-embedding-proof`.
