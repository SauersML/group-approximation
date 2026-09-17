---
rg: 2
id: clean-moody-counts-are-blind-at-every-evaluation-point-proof
kind: route
title: "Triangle equality, argument classes of the evaluation point, and Moody's criterion modulo cyclotomic ideals"
target: clean-moody-counts-are-blind-at-every-evaluation-point
requires:
  - brunnian-4-braids-meet-cyclotomic-burau-congruence-kernels
  - parity-clean-arc-counts-see-only-burau-mod-t-plus-one
artifacts:
  - research/artifacts/burau-cyclotomic-blindness-2026-09-17.md
  - experiments/burau-cyclotomic-blindness-2026-09-17/cyclotomic_blindness.py
  - experiments/burau-cyclotomic-blindness-2026-09-17/run.log
---

Full proof: artifact §§5–7; the ideal-level Moody criterion is Theorem A of
`research/artifacts/zp-burau-parity-t-minus-one-obstruction-2026-09-16.md` (route of
`parity-clean-arc-counts-see-only-burau-mod-t-plus-one`).

1. **Cleanness (Lemma 5.2).** Equality in the triangle inequality for `z_i = ε_i t_0^{k_i}`. Then
   `|A ∩ α| = |𝕄(α, A)(u)|`.
2. **Classification (Lemma 5.3).** `u^{k_i − k_j} = ε_iε_j ∈ {±1}`: odd or infinite order forces equal signs;
   order `2^a r` forces `(N/2) | k_i − k_j` and transfers cleanness to `ζ_{2^a}`.
3. **Blindness transfer (Lemma 6.1).** All ideals involved are self-reciprocal. If `ρ_n(Ψ) ≡ I mod 𝔞` then
   `(1 − t^s)(𝕄_{ΨΓ} − 𝕄_Γ) ∈ 𝔞`: with `𝔞 ⊆ ((t − 1)^2)` the values at `1` agree; with `𝔞 ⊆ (Φ_Q)` the values at
   `ζ_Q` agree because `1 − ζ_Q^s ≠ 0`.
4. **Theorem 2.** `[P_n, P_n] ⊆ G_n((t − 1)^2)`; `ρ_n ∘ f = ρ_4 ⊕ I`; `G_4(𝔞)` is normal, so conjugates and
   powers stay in it; apply steps 1–3.
5. **Theorem 3.** Cancel the unit multiple of the prime `t − 1` from `(1 − t^s)(𝕄_{…} − 𝕄_Γ) ∈ ((t − 1)^2 g)`.
6. **Calibration (§8).** In `B_3` (faithful Burau) the same classes with `u` of order `4r`, `8r`, or odd/infinite
   order are blind to nontrivial Brunnian 3-braids (script check 6), while the `t = −1` case gives nothing in
   `B_3`, consistent with the verified `n = 3` parity proof.
