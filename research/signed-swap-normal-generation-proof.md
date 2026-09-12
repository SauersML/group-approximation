---
rg: 2
id: signed-swap-normal-generation-proof
kind: route
title: Two commutators with the swap and with one unit root
target: signed-swap-normally-generates-elementary-group
requires: []
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
  - research/artifacts/universal-seed-model-test-2026-09-07.md
---

## Proof

Multiplying the three elementary factors gives
`a = [[0,1],[-1,0]] (+) I`, so `a^2 = -I_2 (+) I` and `a^4 = 1`.

On coordinates, `a e_1 = -e_2`, `a e_2 = e_1`, and `a` fixes coordinate
`3`.  So `a E_13 a^(-1) = -E_23` and

```text
a e_13(-r) a^(-1) = e_23(r),
[e_13(r), a] = e_13(r) . a e_13(-r) a^(-1) = e_13(r) e_23(r).
```

Conjugation by `e_12(1)` fixes `e_13(r)`, because `E_12E_13 = E_13E_12 = 0`,
and sends `e_23(r)` to `e_13(r)e_23(r)`, because `[e_12(1), e_23(r)] = e_13(r)`.
So

```text
[e_12(1), e_13(r)e_23(r)]
  = e_13(2r)e_23(r) . e_23(-r)e_13(-r) = e_13(r).
```

Unwinding both commutators writes `e_13(r)` as a product of four conjugates
of `a^(+-1)`, the conjugators being `e_13(r)`, `e_12(1)` and their products.
Conjugating by elementary signed permutation matrices moves the position
`(1,3)` to any `(i,j)` with `i != j`, and those roots generate `EL_m(R)`.

Every coefficient occurring is an integer or the single arbitrary element
`r`, so no characteristic hypothesis enters.
