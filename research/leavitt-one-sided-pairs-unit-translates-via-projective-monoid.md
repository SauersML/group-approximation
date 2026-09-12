---
rg: 2
id: leavitt-one-sided-pairs-unit-translates-via-projective-monoid
kind: route
title: Identify the defect module with R through Bergman's projective monoid and write the unit down
target: leavitt-one-sided-pairs-are-unit-translates-of-s0-t0
requires:
  - binary-leavitt-nonzero-projectives-are-free
artifacts:
  - research/artifacts/leavitt-kaplansky-pair-dichotomy-2026-09-12.md
---

## Why sufficient

This is a second proof of the orbit theorem, gk-kdf-lift's Lemma 1 in the dichotomy
artifact. It uses the imported monoid `V(L_K(1,2)) = {0, [R]}` in place of the
monomial pure-infiniteness lemma.

Let `beta alpha = 1 != alpha beta` in `R` and `e = alpha beta`.

* **The defect module.** `(1 - e)R` is a nonzero finitely generated projective, so the
  prerequisite gives an isomorphism `psi : R -> (1 - e)R`. Put `z = psi(1)` and
  `w = psi^(-1)(1 - e)`. Then `w z = 1`, `z w = 1 - e`, `beta z = 0` and `w alpha = 0`.
* **The unit.** `u = alpha t_0 + z t_1` has inverse `s_0 beta + s_1 w`, and
  `u s_0 = alpha`.
* **The translate.** With `w_0 = u^(-1)`: `w_0 alpha = s_0`, and
  `beta w_0^(-1) = beta u = beta alpha t_0 + beta z t_1 = t_0`.

That is the target.

The elementary route `leavitt-one-sided-pairs-unit-translates-proof` proves the same
statement without the import.
