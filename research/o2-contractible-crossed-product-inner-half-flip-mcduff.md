---
rg: 2
id: o2-contractible-crossed-product-inner-half-flip-mcduff
kind: claim
title: An outer finite group action on O_2 with contractible crossed product has approximately G-inner half-flip and Rokhlin infinite tensor power; it is Rokhlin iff it embeds into its own central sequences
distinct_from:
  outer-actions-on-o2-kk-g-contractible-iff-rokhlin: that identifies contractibility with the Rokhlin property; this shows every action with contractible crossed product is already half-way to strong self-absorption, and isolates the missing McDuff step.
  zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner: that applies Gabe--Szabó uniqueness to the generator against the identity; this applies it to the two factor embeddings into the tensor square.
---

**ESTABLISHED (derivation from Gabe--Szabó, Szabó and Meyer--Nest; standard
outerness facts flagged in the proof).**  Let `G` be a finite group and
`α : G ↷ O_2` pointwise outer with `O_2 ⋊_α G ≃_KK 0`.  Write `D = (O_2, α)`.

1. **The factor embeddings vanish.**  `j = id ⊗ 1` and `k = 1 ⊗ id`, as maps
   `D → D ⊗ D` with the action `α ⊗ α`, are both zero in `KK^G`.  They are
   asymptotically unitarily equivalent through asymptotically invariant
   unitaries.  So `α` has **approximately G-inner half-flip** in Szabó's sense.
2. **The infinite tensor power is the Rokhlin model.**
   `α^(⊗∞) : G ↷ O_2^(⊗∞) ≅ O_2` is strongly self-absorbing and
   KK^G-contractible.  Hence it is conjugate to `id ⊗ μ_G` and has the Rokhlin
   property.
3. **McDuff criterion.**  The following are equivalent:
   - `α` has the Rokhlin property;
   - `α ≃_cc α ⊗ α^(⊗∞)`;
   - there is a unital equivariant \*-homomorphism
     `(O_2, α) → (A_∞ ∩ O_2', α_∞)`, the equivariant McDuff property.

**Consequence for detection.**  By item 3 of
`outer-actions-on-o2-kk-g-contractible-iff-rokhlin`, detection at `p` says
that every such action with `G = Z/p` is equivariantly McDuff.  A phantom is
an outer action on `O_2` that has approximately G-inner half-flip, but not the
McDuff property.  This mirrors a known non-equivariant situation.
Toms--Winter: approximately inner half-flip together with a central unital
copy is strong self-absorption, and `M_n` has inner half-flip without the
central copy.

**Model tests.**
* The Rokhlin model is strongly self-absorbing and satisfies all of item 3.
* Outerness matters in item 2.  The trivial action has contractible crossed
  product and trivial tensor power, which is not Rokhlin.
* What items 1 and 2 use is that `[ι_D] = 0` in `KK^G(C, D) ≅ K_0(O_2 ⋊_α G)`.
  Under Green--Julg, `[ι_D]` is the class of the averaging projection
  `e = |G|^(−1) Σ_g u_g`, whose corner is the fixed-point algebra.  It is not
  the class of `1`, which vanishes for every action on `O_2`.  When the crossed
  product is not contractible, `[e]` can be nonzero, and then `j ≠ 0` and the
  argument stops.

No priority is claimed.

Proof: `o2-contractible-crossed-product-inner-half-flip-mcduff-proof`.
