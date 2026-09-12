---
rg: 2
id: split-identity-minors-triangular-moves-proof
kind: route
title: Clear the corner of a unitriangular minor, then induct along the chain
target: split-identity-minors-survive-triangular-moves
requires: []
artifacts:
  - research/artifacts/state-upgrade-kill-test-2026-09-12.md
---

Section 3 of the artifact.
- **Split minors (Proposition 3.1).** Choose `X_1 (A (+) I_s) W_1 = I_(a+s)` and
  `X_2 (B (+) I_t) W_2 = I_(b+t)`. After permuting rows and columns,
  `T (+) I_(s+t) = [[A (+) I_s, C'], [0, B (+) I_t]]`. Then `diag(X_1, X_2)`, that matrix and
  `diag(W_1, W_2)` multiply to `[[I, D], [0, I]]`, and right multiplication by `[[I, -D], [0, I]]` gives
  the identity.
- **Chains (Corollary 3.2).** Minor steps preserve `⊑`, and `⊑` adds over block sums. So by induction
  `I_(q+1) ⊑ I_q`.
- **Idempotent steps (Remark 3.3).** `T^2 = T` gives `C = AC + CB`. Multiplying by `A` on the left and
  `B` on the right gives `ACB = 2 ACB`, so `ACB = 0`. With `x = AC - CB`, the corner of
  `[[1, x], [0, 1]] T [[1, -x], [0, 1]]` is `C - AC - CB + 2 ACB = 0`.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 28.2 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS. Re-derived independently:*
- *the bordered corner `C'`, and clearing `D` by `[[I, -D], [0, I]]`;*
- *induction from `s = 0`;*
- *`ACB = 2ACB`, and `Ax = AC`, `xB = -CB` in the conjugation;*
- *the `M_2(K)` non-split example by `K`-rank.*
