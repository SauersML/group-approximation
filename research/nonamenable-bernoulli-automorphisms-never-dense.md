---
rg: 2
id: nonamenable-bernoulli-automorphisms-never-dense
kind: claim
title: On every nonamenable group, the automorphisms of every nontrivial finite-base Bernoulli shift are not dense among its endomorphisms
distinct_from:
  spectral-gap-refutes-exactification-on-nonamenable-groups: that proves the failure for base entropy above log 4 on every nonamenable group; this asks for it at every positive base entropy.
  zero-supremum-bernoulli-automorphisms-dense-in-endomorphisms: that asks for density at zero supremum and is equivalent to every group having a positive-entropy action; this asks for failure on all nonamenable groups and all entropies, in contrast with the amenable case.
---

**OPEN.** Let `G` be countably infinite and nonamenable, and let `(L, λ)` be a finite base with `H(λ) > 0`. Then
`Aut_G(X_λ)` is not dense in `End_G(X_λ)`. The stronger form: `X_λ` has no approximate right inverses (ARI, as in
`bernoulli-isomorphism-from-approximate-right-inverses`).

**Why it matters.** Over `Z`, ARI holds by the residual factor theorem, and density of automorphisms is expected
from Ornstein theory. So the claim would separate amenable from nonamenable groups through a single Bernoulli shift
of any entropy. The amenable side is verified here only through the `Z` model test.

**Model tests.**
- It holds for `H(λ) > log 4` on every nonamenable group (item 3 of
  `spectral-gap-refutes-exactification-on-nonamenable-groups`).
- It holds for `H(λ) >= log 4` on groups containing `F_2` (`ornstein-weiss-map-has-no-approximate-right-inverses`).
- It holds for every finite base on nonamenable groups with positive supremum (item 5 of
  `iid-density-iff-collapse-and-endomorphism-density`).
- The open content is therefore at supremum zero with `H(λ) <= log 4`.
- The claim must fail for amenable groups, and over `Z` ARI holds, as required.

## Attempts

- **Sparse Ornstein–Weiss map.** This would give the claim at every positive entropy.
  - Use a base whose symbol marks a site as type 1 (probability `p`), type 2 (probability `p`) or unmarked, with a
    uniform bit at marked sites and extra small-entropy coordinates. Its entropy is `O(h_2(p) + p log 2)`.
  - Suppose, as Borel functions of the unbitted coordinates, there are an essentially free `F_2`-action on the type-1
    points with orbits inside `G`-orbits, and a bijection from type-1 to type-2 points inside orbits.
  - Put `z_g + z_(τ_a g)` at each type-1 site `g`, put `z_g + z_(τ_b g)` at the matched type-2 site, and discard the
    type-2 input bits. The forest argument makes the output i.i.d. given the markers, so this is an endomorphism.
  - The spectral argument, run on the type-1 points, bounds the defects of any right inverse from below, by `p`
    times a positive constant.
- **Where it dies.** At the free `F_2`-action on the type-1 points, which must be measurable in the marker
  coordinates.
  - Restricting Bowen's subrelation (`bernoulli-shifts-are-von-neumann-day`) to the type-1 points gives an ergodic
    treeable relation. By Gaboriau's induction formula its cost is `1 + 1/p`.
  - Extracting a free ergodic `F_2`-action from it needs a Hjorth-type lemma for treeable relations of cost above 1,
    of the kind Gaboriau–Lyons use. Neither the induction formula nor that lemma is imported or checked in this graph.
  - Matching type-1 to type-2 points of equal measure inside orbits is standard for ergodic relations, but it is not
    imported either.
