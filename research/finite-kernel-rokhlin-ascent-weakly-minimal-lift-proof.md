---
rg: 2
id: finite-kernel-rokhlin-ascent-weakly-minimal-lift-proof
kind: route
title: Join the liftable action with large Bernoulli shifts, bound relative entropy below, and apply the equivalence
target: finite-kernel-rokhlin-ascent-from-weakly-minimal-lift
requires:
  - rokhlin-finite-kernel-ascent-iff-liftable-entropy-unbounded
  - seward-weak-containment-relative-entropy-equality
  - abert-weiss-free-actions-weakly-contain-bernoulli
  - seward-rokhlin-entropy-subadditivity
artifacts:
  - research/artifacts/rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md
---

Section 3 of the artifact.

1. **Lifts.** `Y_k = Y_0 × L_k^Q` lifts to `X_0 × L_k^Q`, with `W` acting on `L_k^Q` through `Q`. It is ergodic,
   as the product of an ergodic and a mixing action.
2. **Finite.** By sub-additivity, `h^Rok_Q(Y_k) <= h^Rok_Q(Y_0) + H(L_k)`.
3. **Large.** Relative entropy is at most absolute entropy, so `h^Rok_Q(Y_k) >= H(L_k) - c`, which is unbounded.
4. **Conclusion.** Item (b) of the equivalence holds, so `W` is maximal.
5. **The three cases.**
   - (i) Seward's Theorem 1.2 with `X = L^Q` and `Y = Y_0` gives `h_Q(Y_0 × L^Q | B(Y_0)) = h^Rok_Q(L^Q) = H(L)`,
     using maximality of `Q`.
   - (ii) A Bernoulli shift is weakly contained in every free action (Abért–Weiss), so (i) applies.
   - (iii) `Ω/N` is free, has finite entropy and lifts to `Ω`. The conjecture gives the relative equality directly.
