---
rg: 2
id: stable-finite-actions-extension-sofic-iff-norm-proof
kind: route
title: Theorem 1 gives the sofic direction; Gohla--Thom Theorem 3.4, stability and Corollary 2.14 give vanishing on finite actions
target: stable-finite-actions-extension-sofic-iff-class-norm-vanishes
requires:
  - finite-actions-with-vanishing-class-norm-make-extension-sofic
  - gohla-thom-class-norm-drops-under-weak-containment
artifacts:
  - research/artifacts/sk-deligne-sofic-2026-09-14-part1.md
---

Section 3 of the artifact.
- **`⇐`.** `finite-actions-with-vanishing-class-norm-make-extension-sofic`.
- **`⇒`.** Let `Gamma~` be sofic with limit `A`-free measured `Gamma~`-algebra `Q`, and put `P = Q^A`.
  1. Gohla--Thom Theorem 3.4 (import item 2) gives `theta_*^P(alpha) = 0`.
  2. `P` is the limit action of a sofic approximation of `Gamma`, so by stability it is weakly contained in the finite
     `Gamma`-actions.
  3. Lemma 2.13 and Corollary 2.14 (import item 1) give `0 = |||theta^P(alpha)||| >= inf_X |||theta^X(alpha)|||`.
  4. On finite actions this norm is comparable to `nu_X(alpha)`, through a finite model with the presentation complex
     as 2-skeleton, up to model constants (Gohla--Thom §2.2). So `inf_X nu_X(alpha) = 0`.
