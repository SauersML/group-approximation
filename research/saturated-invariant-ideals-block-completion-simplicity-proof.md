---
rg: 2
id: saturated-invariant-ideals-block-completion-simplicity-proof
kind: route
title: Pass to the quotient recursion and embed the quotient algebra in the quotient completion
target: saturated-invariant-ideals-block-completion-simplicity
requires:
  - nekrashevych-completions-contain-their-coefficients
artifacts:
  - research/artifacts/bh-steinberg-hosts-2026-09-12.md
---

Section 2 of the artifact.

1. **The recursion descends.** `I ⊆ psi^-1(M_d(I))` gives `psi(I) ⊆ M_d(I)`, so
   `psi` induces a unital `psi_bar : B/I -> M_d(B/I)`.
2. **It is injective.** `psi(b) in M_d(I)` implies `b in I`, by saturation.
3. **Quotient completion.** Comparing presentations, `O_psi / J = O_(psi_bar)`.
4. **Embedding.** By `nekrashevych-completions-contain-their-coefficients`(2),
   `B/I` embeds in `O_(psi_bar)`, so `J ∩ B = I`.
5. **Conclusion.** If `I != 0`, then `J != 0`. If `I != B`, then `1 notin J`.
