---
rg: 2
id: braided-v-is-not-inner-amenable-proof
kind: route
title: "Lift a free subgroup of PSL(2,Z) in T to braided V and bound its centralizers"
target: braided-v-is-not-inner-amenable
requires:
  - centralizer-criterion-for-non-inner-amenability
  - psl2z-in-thompson-t-has-amenable-centralizers-in-v
  - braided-v-kernel-elements-have-equivariant-breakpoint-sets
artifacts:
  - research/artifacts/zp-braided-v-not-inner-amenable-2026-09-13.md
---

The full proof is Section 4 of the artifact (Theorem 4.1 and Corollary 4.2).

`Λ ≅ Z_2 * Z_3` has a finite-index free non-abelian subgroup. Lift two free generators of a rank-2
free subgroup to `h_1, h_2 ∈ bV`, and let `H = ⟨h_1, h_2⟩`. π maps H isomorphically onto a free
subgroup of Λ, so H is non-amenable. By `centralizer-criterion-for-non-inner-amenability`, it
suffices to show that `C_H(f)` is amenable for every `f ∈ bV ∖ {1}`, and `C_H(f) ≅ π(C_H(f))`.

- If `π(f) ≠ e`, then `π(C_H(f))` lies in the centralizer of `π(f)` in Λ, which is amenable by
  `psl2z-in-thompson-t-has-amenable-centralizers-in-v`.
- If `f ∈ K ∖ {1}`, then every `h ∈ C_H(f)` satisfies `π(h)(E(f)) = E(f)`, by
  `braided-v-kernel-elements-have-equivariant-breakpoint-sets`. So `φ^{-1} π(h) φ ∈ PSL(2,Z)`
  permutes the finite nonempty set `φ^{-1}(E(f)) ⊆ Q ∪ {∞}`.
  - If this set has at least two points, the permutation determines the element, so
    `π(C_H(f))` is finite.
  - If it has one point, `π(C_H(f))` lies in a point stabilizer of PSL(2,Z), which is infinite
    cyclic.

For the corollary: a nontrivial finite conjugacy class would give an invariant mean, so bV is ICC.
Effros's theorem (arXiv:1609.05086v1, Theorem 3.1) then shows that `L(bV)` lacks property Γ.
