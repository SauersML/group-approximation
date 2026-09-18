---
rg: 2
id: sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget
kind: claim
title: The SL_3(Z) Toeplitz harmonic ring meets both clauses of the UHF K-budget, in every full corner and for every unit
distinct_from:
  sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational: that proves the ring is finitely generated, simple and K_1-rational, kills K_2(Q) at the unit and in block corners, and trivializes the symbols of block units; this asks for the remaining corners and units.
  q-algebra-with-fp-simple-projective-elementary-group: that is the host premise, which also needs PE_N finitely presented and simple; this is only the K-theoretic necessary part, for one candidate.
artifacts:
  - research/artifacts/gq-deep-adelic-1-sl3-remnant.md
---

**OPEN, and off the host route (2026-09-18).** `bounded-harmonic-rings-are-not-finitely-presented`
(lane gq-steinberg-q, 1111ca113) shows that neither `R_T` nor any `E_N(R_T)`, `N >= 3`, is finitely presented. R1
and R2 below are necessary conditions only for a finitely presented `E_N`, so they no longer bear on
`gl-n-q-embeds-in-fp-simple-group` through `R_T`. They remain open as K-theory questions about this ring.

Let `R_T` be the ring of `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`. Then:

- **(R1) Full corners.** For every nonzero idempotent `e ∈ R_T`, the image of
  `K_2(Q) -> K_2(e R_T e)` is finite. This is required by `full-corners-must-kill-rational-k2-symbols`
  when `E_N(R_T)` is finitely presented.
- **(R2) Rational symbols.** The symbols `{λ, x}`, `λ ∈ Q^x`, `x ∈ R_T^x`, generate a finitely generated
  subgroup of `K_2(R_T)`. This is required by `infinitely-generated-symbols-block-fp-elementary-groups`.

## Known

- **(K1).** Detection of `Q^x` in `K_1` with kernel in `{±1}`.
- **R1 for the unit and for every block.** Every corner at a union of blocks, i.e. the preimage of an
  odometer clopen, is matricially divisible, so it kills `K_2(Q)`.
- **R2 for the group units `u_γ` and for block units** `χ_C u_γ + (1 - χ_C)`, `γ ∈ Γ(d)`, and all
  their products. This uses the vanishing transfer `sl3-congruence-transfer-kills-abelianization`.

## What remains

- **R1 for non-saturated clopens.** The letter cylinders `[a]` of `X` are not unions of fibres of
  `π : X -> K`, so the class `[χ_[a]] ∈ K_0(R_T)` can differ from pulled-back classes by an
  "infinitesimal" part that need not be divisible.
  - A sufficient condition: every clopen `A ⊆ X` is equidecomposable in `R_T`, by pieces `χ_D u_g`,
    into `n` equivalent pieces for `n` cofinal. This is a comparison and divisibility property of the
    groupoid `Γ ⋉ X`.
  - For the odometer itself it is automatic; for Toeplitz extensions over a group with property (T)
    it is unknown.
- **R2 for all units.** The combinatorial units with non-saturated pieces, i.e. elements of the
  topological full group of `Γ ⋉ X`, have `K_1` classes governed by `H_1(Γ; C(X, Z))`. Only the
  odometer part `H_1(Γ; C(K, Z)) = 0` is known. Non-combinatorial units, e.g. those built from the
  harmonic coefficient ring, are uncontrolled.
- **A cleaner test ring.** On the odometer `K` itself, the ring `R_K = ⟨u_s^(±1), f⟩` contains `Q`
  (`harmonic-elimination-puts-q-in-odometer-crossed-products`) and is tracial through Haar measure. All
  its clopen classes are divisible, so R1 at clopens is automatic. But its coefficient ring may have
  no idempotents beyond `0, 1`, and neither its simplicity nor the divisibility of `[1]` is known. See
  the artifact.

## Attempts

1. **Towards R2 through the coefficient ring (2026-09-18, not landed as a node).** Choose `x_∞` with a
   one-point fibre `π^(-1)(x_∞)`, which exists because `X` is an almost one-to-one extension of `K`
   (Cecchi Bernales–Cortez–Gómez). Then the coefficient ring `B = R_T ∩ C(X,Q)` has two properties:
   - every element of `B` is locally constant off finitely many orbit points, and near each of them is
     a polynomial in one harmonic function;
   - so `B^x = LC(X, Q^x)`, and each finite stage is an extension of `Π Q[t]` by an ideal with local
     units.

   Tor-unital excision (Suslin, as quoted in Tamme, arXiv:1703.03331) and homotopy invariance of
   `K(Q[t])` would then give `K_*(LC(X,Q)) ≅ K_*(B)`, and the same for `B ⋊ V` with `V` finite. That
   would reduce R2 to the Steinberg-algebra ring `LC(X,Q) ⋊ Γ` and to `H_*(Γ; C(X,Z))`, if also
   infinite virtually cyclic `V` and a Farrell–Jones comparison were handled. Not pursued once 1111ca113
   removed `R_T` from the host route.
