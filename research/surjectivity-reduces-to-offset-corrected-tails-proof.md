---
rg: 2
id: surjectivity-reduces-to-offset-corrected-tails-proof
kind: route
title: Straighten each row with its offset included and read surjectivity off the zero fiber
target: surjectivity-reduces-to-offset-corrected-tails
requires:
  - nonlinear-certificate-fibers-are-all-surjective-or-all-strict
artifacts:
  - research/artifacts/offset-corrected-peeling-2026-09-12.md
---

Section 2 of the artifact.

- **Type (O).** `E_a(X_a, Y) = (row_a, Y)` is a bijective automaton, with local
  inverse by Curtis--Hedlund--Lyndon. `D_a = F^(a) o E_a^(-1)` leaves the row value
  `Z` unchanged, and its fiber at `Z = 0` is the corrected tail. The certificate-fiber
  dichotomy gives injectivity of the tail, and `F^(a)` is surjective iff the tail is.
- **Type (Z).** `F^(a)(0, Y) = (0, F^(a+1)(Y))` gives injectivity of the tail. The
  two-block lemma, reproved in the artifact from the same dichotomy, makes `F^(a)`
  surjective once the tail is.
- **Induction.** Downward from the last tail.
- **Strictly upper triangular controllers.** A product of `d` strictly upper
  triangular matrices in one flag vanishes, so the own-linear part is unipotent
  with a finite local inverse series.
