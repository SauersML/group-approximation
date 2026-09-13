---
rg: 2
id: cartan-invariant-zp-actions-on-o2-have-trivial-action-element
kind: claim
title: A Z/p-action on O_2 fixing a Cartan subalgebra has trivial action element in KK^G, so equivariant phantoms fix no Cartan subalgebra
distinct_from:
  zp-o2-generator-kk-class-is-twisted-asymptotic-innerness: that characterizes each value of the action element by twisted asymptotic innerness; this proves the value 1 for every action with an invariant Cartan subalgebra.
  cartan-respecting-o2-automorphisms-give-uct-crossed-products: that concludes the UCT for the crossed product only; this concludes triviality of the generator in KK^G and hence Rokhlin rigidity for these actions.
  bootstrap-class-zp-actions-on-o2-fix-a-cartan: that goes from the equivariant bootstrap class to an invariant Cartan subalgebra; this goes the other way and adds the consequences for the action element and for phantoms.
---

**OPEN (lane ex3-uct-cartan-fence, 2026-09-13).**  Let `p` be prime,
`G = Z/p` with generator `ω`, and `α : G ↷ O_2` an action with `α_ω(C) = C` for
some Cartan subalgebra `C ⊆ O_2`.  Put `E = (O_2, α)` and
`θ = [α_ω] ∈ KK^G(E, E)`.  Claimed consequences:

1. `θ = 1`.
2. If `α` is pointwise outer and `O_2 ⋊_α G ≃_KK 0`, then `α` has the Rokhlin
   property.
3. So an equivariant phantom leaves no Cartan subalgebra invariant.  Such a
   phantom is a pointwise outer action on `O_2` with contractible crossed
   product that is not Rokhlin.  By
   `zp-o2-generator-kk-class-is-twisted-asymptotic-innerness` its generator is
   `χ^k`-twisted asymptotically inner and never untwisted.
4. With `bootstrap-class-zp-actions-on-o2-fix-a-cartan` and Barlak--Li II
   Theorem 4.16, the UCT at `p` holds iff every outer strongly approximately
   inner `Z/p`-action on `O_2` is in `B^G`.  This needs no detection
   hypothesis.

Route: `cartan-fence-zp-o2-trivial-action-element-via-bootstrap`.  It requires
the open claim `cartan-invariant-finite-actions-in-equivariant-bootstrap`, so it
does not fire yet.
