---
rg: 2
id: full-idempotent-properly-infinite-unit-proof
kind: route
title: Build the two copies from the fullness witnesses and read the witness back off
target: full-idempotent-ring-has-properly-infinite-unit
requires: []
artifacts:
  - research/artifacts/rank-two-descent-review-2026-09-07.md
---

## Proof

**(1) implies (2).**  Put `e = 1-st`, so `e^2 = e`, `es = 0`, `te = 0`, and
choose `sum_(j<m) a_j e b_j = 1`.  Set

```text
v_0 = s^m,  w_0 = t^m,
v_1 = sum_(j<m) s^j e b_j,   w_1 = sum_(j<m) a_j e t^j.
```

Since `ts = 1`, `t^i s^j` equals `s^(j-i)` when `j >= i` and `t^(i-j)` when
`i >= j`, so

```text
e t^i s^j e = delta_(ij) e        (0 <= i,j < m),
```

the off-diagonal cases dying on `es = 0` and `te = 0`.  Then
`w_0v_0 = t^m s^m = 1`, `w_1v_1 = sum_i a_i e b_i = 1`,
`w_0v_1 = sum_j t^(m-j) e b_j = 0` and
`w_1v_0 = sum_i a_i e s^(m-i) = 0`.

**(2) implies (1).**  Take `s = v_0`, `t = w_0`, so `ts = 1`, and

```text
w_1(1 - v_0w_0)v_1 = w_1v_1 - (w_1v_0)(w_0v_1) = 1,
```

so `1` lies in `R(1-st)R`.

**Proper infiniteness.**  `p_i = v_iw_i` satisfies `p_i^2 = v_i(w_iv_i)w_i = p_i`
and `p_0p_1 = v_0(w_0v_1)w_1 = 0`, and `w_i, v_i` implement `p_i ~ 1`.
