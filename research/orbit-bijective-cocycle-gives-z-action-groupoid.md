---
rg: 2
id: orbit-bijective-cocycle-gives-z-action-groupoid
kind: claim
title: An ample groupoid with a continuous Z-valued cocycle bijective on every source fibre is a Z-action groupoid
---
**Statement.** Let G be an ample Hausdorff groupoid with compact unit space, and c: G → Z a continuous homomorphism
whose restriction c|_{s^{-1}(x)}: s^{-1}(x) → Z is a bijection for every unit x. Then:
- B_1 = c^{-1}(1) is a full compact open bisection;
- T = r∘(s|_{B_1})^{-1} is a homeomorphism of G^(0);
- γ ↦ (c(γ), s(γ)) is an isomorphism of topological groupoids G → Z ⋉_T G^(0).

**Consequences.** Every isotropy group of such a G is a subgroup of Z. So an effective groupoid with a nontrivial
finite isotropy group carries no such cocycle. Example: the dihedral Sturmian groupoid in
`research/artifacts/sk-cartan-counterexample-2026-09-13-part1.md` §5.

**Credit.** Folklore. Novelty check: a grep of main only.

Proof route: `orbit-bijective-cocycle-gives-z-action-groupoid-proof`.
