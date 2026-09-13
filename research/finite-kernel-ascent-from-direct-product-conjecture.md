---
rg: 2
id: finite-kernel-ascent-from-direct-product-conjecture
kind: route
title: Seward's direct-product equality applied to the twisted section action gives the finite-kernel ascent
target: rokhlin-maximality-ascends-finite-normal-extensions
requires:
  - seward-direct-product-relative-rokhlin-entropy-conjecture
  - finite-kernel-rokhlin-ascent-from-weakly-minimal-lift
  - bernoulli-rokhlin-maximality-passes-to-subgroups
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
artifacts:
  - research/artifacts/rokhlin-finite-kernel-ascent-equivalence-2026-09-13.md
---

1. **Finitely generated quotient.** `Ω/N` is a free `Q`-action of finite entropy that lifts to `Ω`. The conjecture
   gives `h_Q(Ω/N × L^Q | B(Ω/N)) = H(L)`, which is case (iii) of `finite-kernel-rokhlin-ascent-from-weakly-minimal-lift`.
   So `W` is maximal.
2. **General quotient.** A locally finite `W` is amenable and maximal. Otherwise `W` is the directed union of the
   finitely generated subgroups `W_i` containing `N` and a fixed infinite finitely generated subgroup.
   - Each `W_i/N <= Q` is maximal by subgroup permanence.
   - By step 1 each `W_i` is maximal.
   - Maximality is closed under directed unions.
