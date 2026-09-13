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

1. Let `1 ≠ Φ ∈ Brun_4`. `Brun_4` is normal, so any conjugate `Φ_0` is still Brunnian, and
   `Φ_0 ∈ ker ρ_4` iff `Φ ∈ ker ρ_4`.
2. By `brunnian-four-braids-have-five-strand-moody-witness`, some conjugate `Φ_0` and push map
   `Γ ∈ K_5` satisfy `𝕄_{f(Φ_0)·Γ} ≠ 𝕄_Γ`.
3. By `moody-polynomial-change-certifies-burau-nonkernel` with `n = 5`, `f(Φ_0) ∉ ker ρ_5`.
4. By `burau-kernel-restricts-along-strand-inclusion`, `Φ_0 ∉ ker ρ_4`, so `Φ ∉ ker ρ_4`. ∎
