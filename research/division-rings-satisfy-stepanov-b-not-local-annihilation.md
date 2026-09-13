---
rg: 2
id: division-rings-satisfy-stepanov-b-not-local-annihilation
kind: claim
title: Simple Artinian rings satisfy Stepanov's linear-dependence hypotheses but never have local annihilation
distinct_from:
  stepanov-linear-dependence-standard-normal-structure: that is Stepanov's theorem, standard normal structure from conditions (a) and (b); this compares its hypothesis (b) with local annihilation and separates them.
  local-annihilation-makes-projective-el-simple: that is the simplicity criterion from local annihilation; this shows its hypothesis is not implied by Stepanov's (b).
artifacts:
  - research/artifacts/un-stepanov-credit-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `R = M_m(D)` with `D` a division ring and `m ≥ 1`, so `R` is simple Artinian, and
let `n ≥ 3`.

1. **Stepanov's (a) and (b) hold for `R`.** The only proper two-sided ideal is `0`, so (a) is trivial. For (b), take
   `b = 1`. The conditions `α_i = 0` and `(uα)_j = 0` on a column `α ∈ R^n` supported in its first `D`-column are
   `2m` right-linear equations over `D` in `nm ≥ 3m` unknowns, so a nonzero solution exists.
2. **`R` does not have local annihilation.** Take `F` to be the `m²` matrix units. If `t ≠ 0` and `t E_(ij) s = 0` for
   all `i, j`, some entry `t_(pi)` is invertible in `D`, which forces every entry of `s` to vanish. So `S_F = {0}`,
   and its closure is `0 ≠ R`.

**Consequence for credit.** Stepanov's condition (b) does not imply local annihilation. So the ring criterion
`local-annihilation-makes-projective-el-simple` is not a weakening of Stepanov's theorem: Stepanov covers every simple
Artinian ring, while local annihilation covers none of them. Whether local annihilation implies (b) is the open claim
`local-annihilation-implies-stepanov-condition-b`.
