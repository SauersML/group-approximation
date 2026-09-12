---
rg: 2
id: cartan-respecting-o2-automorphisms-give-uct-crossed-products
kind: claim
title: Finite-order automorphisms of O_2 from the normalizer of D_2 or from tensor flips give UCT crossed products
invalidates:
  - non-uct-witness-from-cartan-respecting-automorphism
distinct_from:
  barlak-li-cartan-subalgebras-force-uct: that is the general permanence theorem for Cartan-invariant actions; this identifies two concrete automorphism families of O_2 it covers, including the Thompson group V automorphisms native to the Leavitt region.
artifacts:
  - research/artifacts/stw-uct-reduction-map-2026-09-11.md
---

**ESTABLISHED (derivation, this repository).**  Let `α` be an automorphism of
`O_2` of finite order `n` (a `Z_n`-action).  Then `O_2 ⋊_α Z_n` satisfies the UCT
whenever `α` leaves some Cartan subalgebra of `O_2` globally invariant.  In
particular this holds for:

1. **Normalizer gauge automorphisms.**  `α = λ_u`, `λ_u(s_i) = u s_i`, with `u`
   in the unitary normalizer of the canonical masa `D_2`.  This family includes
   every unitary of the Thompson group `V ⊂ U(O_2)`, as permutations of prefix
   cylinders, and every unitary of `D_2`.
2. **Tensor flips.**  `α = θ ∘ σ ∘ θ^{-1}`, where `σ(a ⊗ b) = b ⊗ a` is the flip
   of `O_2 ⊗ O_2` and `θ : O_2 ⊗ O_2 → O_2` is any isomorphism.

Proof: `cartan-respecting-o2-automorphisms-proof`.

So neither family can produce a UCT counterexample through
`O_2 ⋊ Z_p`.  A candidate must be an order-`p` automorphism with no invariant
Cartan subalgebra.
