---
rg: 2
id: triangular-identity-certificate-criterion-proof
kind: route
title: Goodearl–Handelman on the monoid of matrices modulo domination, then absorption of the unit
target: sylvester-rank-functions-iff-no-triangular-certificate
requires: []
artifacts:
  - research/artifacts/state-upgrade-kill-test-2026-09-12.md
---

Section 2 of the artifact (Theorems 2.1 and 2.2).
- **Axioms as monotonicity.** Sylvester rank functions are exactly the matrix states monotone for
  minors and triangular moves: `MN <~ M, N` gives the product axiom, and `A (+) B <=_T T` the
  triangular axiom.
- **Goodearl–Handelman.** On the Grothendieck group of `Mat(A)/~`, with cone
  `P = {[N] - [M] : M <=_T N}` and order unit `[I_1]`, a state exists iff `-[I_1]` is not in `P`. This
  is census Theorem A(b), whose proof uses only the cone and order-unit properties.
- **Absorption.** `-[I_1]` is in `P` iff `I_1 (+) X <=_T X` for some `X`. Iterating gives
  `I_(q+1) <=_T I_(q+1) (+) X <=_T X <~ I_q`, with `q` the number of columns of `X`.
- **Minors only.** The same argument with `<~` gives the rank condition.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 28.1 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the axioms as monotonicity, with zero matrices of all sizes mutual minors;*
- *the order unit `X <~ I_c <~ I_c (+) Y`;*
- *the state criterion via `-ku ∈ P ⟹ -u ∈ P` and the one-step extension lemma;*
- *absorption `N (+) I_1 (+) K ~ M (+) K`, the chain relation, and the rank-condition case.*
