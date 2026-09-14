---
rg: 2
id: leavitt-one-sided-pairs-unit-translates-proof
kind: route
title: Equate the defect with s_1 t_1 and build the translating unit from both equivalences
target: leavitt-one-sided-pairs-are-unit-translates-of-s0-t0
requires:
  - binary-leavitt-algebra-is-purely-infinite-by-monomials
artifacts:
  - research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md
---

## Why sufficient

Put `p = 1 - alpha beta` and `p' = s_1 t_1`.

* **Lemma 2 of the artifact.** The monomial lemma gives `mu p nu = 1`, so `p`
  dominates an idempotent equivalent to `1`, and `pR ~= pR (+) R` by
  `R ~= R (+) R`. Also `R = alpha beta R (+) pR ~= R (+) pR`. Hence `pR ~= R`,
  and composing with `s_1, t_1` gives `x` in `pRp'`, `y` in `p'Rp` with
  `xy = p`, `yx = p'`.
* **Theorem 3.** Using `beta p = 0`, `p alpha = 0`, `t_0 p' = 0` and
  `p' s_0 = 0`, the elements `w = s_0 beta + y` and `w' = alpha t_0 + x` satisfy
  `w w' = s_0 t_0 + s_1 t_1 = 1` and `w' w = alpha beta + p = 1`. Then
  `w alpha = s_0` and `beta w' = t_0`.
