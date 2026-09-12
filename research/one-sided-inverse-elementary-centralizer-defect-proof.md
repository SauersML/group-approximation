---
rg: 2
id: one-sided-inverse-elementary-centralizer-defect-proof
kind: route
title: Multiply out the comb compressor and the one-coordinate centralizer word
target: one-sided-inverse-elementary-centralizer-defect
requires: []
artifacts:
  - research/artifacts/full-complementary-idempotent-check-2026-09-05.md
  - GroupApproximation/Leavitt/RankFourCompressors.lean
---

## Why sufficient

Direct matrix computation using only `ts = 1`.  The `(i,4)` block of `u_i`
is `[[s, e],[0, t]]`; multiplying the three pieces gives

```text
u = [[s,0,0,e],[0,s,0,et],[0,0,s,et²],[0,0,0,t³]],
u⁻¹ = [[t,0,0,0],[0,t,0,0],[0,0,t,0],[e,se,s²e,s³]],
```

and `u diag(A,1) u⁻¹ = diag(eI_3 + sAt, 1)` because the column
`v = (e, et, et²)ᵀ` and row `w = (e, se, s²e)` satisfy `v w = e I_3`,
`v s³ = 0`, `t³ w = 0`.  For `c`, the commutator in the `(1,4)` block is
`[[1,0],[e,1]] [[1,t],[0,1]] [[1,0],[-e,1]] [[1,-t],[0,1]] = [[1,0],[0,1+et]]`
since `te = 0`.  Then `u c u⁻¹` has top-left block
`st I_3 + v' w` with `v' = v(1+et) = (e+et, et, et²)ᵀ`, and
`v' w = e I_3 + e E_{12}`, giving `e_{12}(e)`.  The last identity is the
Steinberg relation `[e_{12}(e), e_{23}(1)] = e_{13}(e)`.

Every identity was also verified by the exact noncommutative computation in
the artifact (free algebra modulo `ts → 1`, generic `A`).  The compressor
half is machine-checked in `RankFourCompressors.lean` (`compressor_val`);
the centralizer half has no Lean carrier yet.
