---
rg: 2
id: brunnian-four-braids-avoid-burau-kernel-via-moody
kind: route
title: "Brunnian 4-braids avoid the Burau kernel: five-strand Moody witnesses, Moody's criterion, and kernel restriction along the strand inclusion"
target: brunnian-four-braids-avoid-burau-kernel
requires:
  - brunnian-four-braids-have-five-strand-moody-witness
  - moody-polynomial-change-certifies-burau-nonkernel
  - burau-kernel-restricts-along-strand-inclusion
---

Architecture of Theorem 6.6 of arXiv:2607.05283v1, with every implication's direction checked
(artifact `research/artifacts/zp-burau-four-strand-mechanism-2026-09-13.md`, §1–2):

1. Let `1 ≠ Φ ∈ Brun_4`. By `brunnian-four-braids-have-five-strand-moody-witness`, there are
   `k ≥ 1`, a conjugate `Φ_0` of `Φ^k`, and a push map `Γ ∈ K_5` with `𝕄_{f(Φ_0)·Γ} ≠ 𝕄_Γ`.
2. By `moody-polynomial-change-certifies-burau-nonkernel` with `n = 5`, `f(Φ_0) ∉ ker ρ_5`.
3. By `burau-kernel-restricts-along-strand-inclusion`, `Φ_0 ∉ ker ρ_4`.
4. `ker ρ_4` is normal, so `Φ^k ∉ ker ρ_4`. It is a subgroup, so `Φ ∉ ker ρ_4`. ∎
