---
rg: 2
id: layered-weil-actor-models-non-roundable-and-normalizing-proof
kind: route
title: Layer Schrödinger--Weil representations along the symplectic compressor, then read rounding off the central fixed mass and normalization off the layer algebra
target: layered-weil-actor-models-non-roundable-and-normalizing
requires: [rf-kazhdan-group-not-flexibly-hs-stable, kazhdan-cover-models-round-iff-kernel-fixed-mass-one, compressor-extension-makes-roundable-vertex-part-invariant]
artifacts:
  - research/artifacts/ex2-ft-layered-weil-calibration-2026-09-13.md
---

Full derivation: artifact §§1–5. Standard imports:
- Stone--von Neumann for finite Heisenberg groups of odd order;
- perfectness and trivial Schur multiplier of `Sp_(2g)(F_ℓ)` for `g >= 2`, `ℓ >= 5`.

1. **The Heisenberg cover** `Γ~`, with cocycle `ω(v,Aw)` and central `z`, is Kazhdan
   (`rf-kazhdan-group-not-flexibly-hs-stable`). `φ~(v,s,A) = (pv, p^2 s, A)` covers `φ` and sends `z` to
   `z^(p^2)`.
2. **Representations.** Mod `ℓ`, `S~_c = S_c ⋊ W_c` is irreducible with central character `e(c/ℓ)`.
   - Uniqueness of the Schrödinger representation and of the Weil lift gives unitaries `U_c` with
     `U_c S~_c(φ~x) U_c^* = S~_(p^2 c)(x)`.
   - `Ad W_c(A)` permutes the orthogonal basis `S_c(v,0)`. So `|tr W_c(A)|^2 = ℓ^(dim ker(A-1))`, and
     `|tr S~_c(v,s,A)| <= ℓ^(-rank(A-1)/2)` in normalized trace for `A ≠ 1`. The trace is 0 for `A = 1`, `v ≠ 0`.
3. **The model.**
   - **Vertex defects** are the central scalars `e(c_j ω(v,Aw)/ℓ)`, and `c_j < ℓ^(1/2)`.
   - **The HNN relation** is exact off the wrap-around layer, so its defect is `<= 2/√L`.
   - **Trace.** Words `t^(-a)γt^b` with `a ≠ b` shift layers. Words with `a = b` are block diagonal, with blocks
     conjugate to `S~_(c_j)(sγ)`. So `σ` is a trace-preserving homomorphism of `V`.
4. **Total non-roundability.**
   - `ρ(z)^2` is a group commutator of `σ(Γ)`, and `ρ(z)` is a continuous function of it. So every
     `P ∈ R` commutes with `ρ(Γ~)`.
   - The Kazhdan corner lemma for `Γ~` makes `P` exact at coordinates.
   - The corner is pulled back from `Γ~` with (KC1) and `Fix_z = 0`. So it does not round, by
     `kazhdan-cover-models-round-iff-kernel-fixed-mass-one`.
   - Lemma C of `compressor-extension-makes-roundable-vertex-part-invariant` gives `d(σ) >= κ`.
5. **Normalization.**
   - By step 4 and Kazhdan exactness, `R = prod_U ρ_ℓ(Γ~)'`.
   - The layers are irreducible and pairwise inequivalent, so `R` is the layer algebra.
   - The shift permutes layers, and conjugates of vertex elements are block diagonal. Hence
     `σ(t)Rσ(t)^* = R` and `R = σ(N_V)' ∩ M`.
