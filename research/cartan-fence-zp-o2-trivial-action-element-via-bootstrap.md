---
rg: 2
id: cartan-fence-zp-o2-trivial-action-element-via-bootstrap
kind: route
title: Equivariant bootstrap membership of Cartan-invariant actions makes the action element trivial and forces Rokhlin rigidity
target: cartan-invariant-zp-actions-on-o2-have-trivial-action-element
requires:
  - cartan-invariant-finite-actions-in-equivariant-bootstrap
  - zp-restriction-trivial-splits-cellular-plus-phantom
  - outer-actions-on-o2-kk-g-contractible-iff-rokhlin
  - zp-o2-generator-kk-class-is-twisted-asymptotic-innerness
  - bootstrap-class-zp-actions-on-o2-fix-a-cartan
  - barlak-li-p-half-iff-zp-actions-fix-cartan
---

Let `α : G = Z/p ↷ O_2` fix a Cartan subalgebra `C` globally, with
`E = (O_2, α)` and `θ = [α_ω]`.

1. **`θ = 1`.**  `O_2` is separable and nuclear, so
   `cartan-invariant-finite-actions-in-equivariant-bootstrap` gives `E ∈ B^G`.
   `Res E = O_2 ≃_KK 0`.  By item 5 of
   `zp-restriction-trivial-splits-cellular-plus-phantom`, when `Res E ≃ 0` we
   have `E ∈ B^G` iff `θ_E = 1` and `E ⋊ G ∈ B`.  So `θ_E = 1`.
2. **Rokhlin rigidity.**  Suppose `α` is pointwise outer and
   `O_2 ⋊_α G ≃_KK 0`.  By item 2 of the same node, `1 − θ_E` is invertible in
   `KK^G(E, E)`.  Since `θ_E = 1`, this says `0` is invertible, so
   `KK^G(E, E) = 0` and `E ≃_(KK^G) 0`.  By
   `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, `α` is Rokhlin.
3. **Phantoms.**  Item 3 of the target is the contrapositive of item 2.  Item 4
   of `zp-o2-generator-kk-class-is-twisted-asymptotic-innerness` splits a
   phantom into Galois components with `θ = χ^k`, `k ≠ 0`.  Each component is
   `χ^k`-twisted asymptotically inner and not untwisted.
4. **UCT at `p`.**  Barlak--Li II Theorem 4.16 states (i) ⟺ (iii), where
   (i) is the UCT for separable nuclear `A ≃_KK A ⊗ M_(p^∞)`, and (iii) says every
   outer strongly approximately inner `Z_p`-action on `O_2` fixes a Cartan
   subalgebra (`barlak-li-p-half-iff-zp-actions-fix-cartan`).
   * For such actions, a fixed Cartan subalgebra implies `B^G` by the first
     requirement.
   * `B^G` implies a fixed Cartan subalgebra by
     `bootstrap-class-zp-actions-on-o2-fix-a-cartan`, with `n = 1`.

   So (iii) is equivalent to: every outer strongly approximately inner
   `Z_p`-action on `O_2` lies in `B^G`.
