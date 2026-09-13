---
rg: 2
id: rokhlin-maximality-finite-quotient-descent-proof
kind: route
title: Push high-entropy free actions down to the quotient with the quotient formula, then pass to directed unions
target: rokhlin-maximality-descends-along-finite-normal-quotients
requires:
  - rokhlin-entropy-quotient-formula-for-finite-normal-subgroups
  - seward-per-group-rokhlin-entropy-of-bernoulli-shifts
  - bernoulli-rokhlin-maximality-passes-to-subgroups
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
artifacts:
  - research/artifacts/rokhlin-finite-kernel-quotient-formula-2026-09-13.md
---

Section 3 of the artifact.

1. **Maximality is INF.** By Seward's Theorem 1.10, `h^Rok_G(L^G) = min{H(L), h_sup(G)}`. So maximality at every
   alphabet is `h_sup(G) = ∞`.
2. **Finitely generated quotient.** Fix `C` and a free ergodic `W`-action `X` with `C < h^Rok_W(X) < ∞`. The quotient
   formula makes `X/N` a free ergodic `Q`-action with `|N| C < h^Rok_Q(X/N) <= |N| h^Rok_W(X) + r log|N| < ∞`. So
   `h_sup(Q) = ∞`.
3. **General quotient.** A locally finite `Q` is amenable, hence sofic and maximal. Otherwise write `Q` as the
   directed union of the finitely generated `Q_i` containing a fixed infinite finitely generated subgroup.
   - Each `π^-1(Q_i)` is an infinite, finitely generated subgroup of `W` containing `N`, so it is maximal.
   - Step 2 makes each `Q_i` maximal.
   - Maximality is closed under directed unions.
