---
rg: 2
id: finite-normal-p-subgroups-modular-stable-finiteness-proof
kind: route
title: Nilpotent augmentation kernels carry stable finiteness across finite normal p-subgroups
target: finite-normal-p-subgroups-preserve-modular-stable-finiteness
requires: []
artifacts:
  - research/artifacts/deligne-triple-cover-surjunctivity-2026-09-12.md
---

Section 1 of the artifact.

1. **Kernel.** With a transversal `T` of `E/N`, `k[E] = sum_t t k[N]`, and an element lies in the kernel
   of `k[E] -> k[E/N]` iff each coefficient `a_t` has augmentation zero. So the kernel is
   `J = k[E] omega`. Normality gives `g omega g^(-1) = omega`, so `J = omega k[E]` and
   `J^m = omega^m k[E]` (Lemma 1.1).
2. **Nilpotence.** Induct on `|N|` through a central `c` of order `p`. `u = c - 1` is central with
   `u^p = 0`, the kernel of `k[N] -> k[N/<c>]` is `u k[N]`, and the induction hypothesis gives
   `omega^(|N|/p) <= u k[N]`, so `omega^|N| = 0` (Lemma 1.2).
3. **Lifting.** For a two-sided ideal `I` with `I^m = 0`, and at every matrix size:
   - a one-sided inverse pair `ab = 1` in `R` has `1 - ba` an idempotent in `I`, hence zero;
   - a pair `abar bbar = 1` in `R/I` lifts to `ab = 1 + i`, a unit, so `b' = b (ab)^(-1)` is a right
     inverse of `a` with image `bbar` (Lemma 1.3).
4. Apply step 3 to `R = k[E]` and `I = J`, with `J^|N| = 0` from steps 1 and 2.
