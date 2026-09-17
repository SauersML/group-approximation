---
rg: 2
id: brunnian-4-braids-meet-cyclotomic-burau-congruence-kernels-proof
kind: route
title: "Twist congruences, the (t−1)-adic filtration of the pure braid group, and pseudo-Anosov commutators"
target: brunnian-4-braids-meet-cyclotomic-burau-congruence-kernels
requires:
  - brunnian-four-braids-are-pseudo-anosov
artifacts:
  - research/artifacts/burau-cyclotomic-blindness-2026-09-17.md
  - experiments/burau-cyclotomic-blindness-2026-09-17/cyclotomic_blindness.py
  - experiments/burau-cyclotomic-blindness-2026-09-17/run.log
---

Full proof: artifact §§2–4.

1. **Twist congruences (§2, Lemmas 2.1–2.3).** `ρ(σ_1^2) = I + (t − 1)N_2` with `N_2^2 = (1 + t)N_2`, and
   `ρ((σ_1σ_2)^3) = I + (t − 1)N_3` with `N_3^2 = (1 + t + t^2)N_3`. The binomial theorem gives
   `ρ(σ_1^{2j}) = I + ((t^{2j} − 1)/Φ_2) N_2` and the analogue for three-point twists. Since `t^N − 1` is
   squarefree, `ρ_4(X_q) ≡ I mod Φ_q` (Corollary 2.4).
2. **Filtration (§3).** Commutators multiply ideals (Lemma 3.1); `ρ_n(P_n) ≡ I mod (t − 1)` (Lemma 3.2);
   `Brun_n ⊆ [P_n, P_n]` via the pairwise forgetful maps `P_n → P_2` (Lemma 3.3). So `ρ_4(b) ≡ I mod (t − 1)^2`.
3. **Congruence (§4).** Induction with Lemma 3.1.
4. **Brunnian (§4).** Normality of `Brun_4`.
5. **Nontrivial (§4).** If `[T_c^m, Ψ] = 1` with `1 ≠ Ψ ∈ Brun_4`, then `T_{Ψ(c)}^m = T_c^m` in `Mod(S_{0,5})`, so
   `Ψ(c) = c`, contradicting `brunnian-four-braids-are-pseudo-anosov`.
6. **Certificate.** `cyclotomic_blindness.py` (exact arithmetic, exit 0, `ALL CHECKS PASS: True`) confirms the
   congruence and `ρ_4(Ψ_g) ≠ I` for `g = Φ_q`, `q = 2, …, 24`, and for the jets `Φ_2^2`, `Φ_4^2Φ_3`,
   `Φ_1Φ_2^2Φ_8`.
