---
rg: 2
id: vd-poly-dehn-via-square-word-projection
kind: route
title: Polynomial Dehn function of V_d from the square-word reduction and polynomial square-word area
target: higman-thompson-vd-has-polynomial-dehn-function
requires:
  - vd-dehn-bounded-by-standard-square-word-area
  - vd-standard-square-words-have-polynomial-area
---

By `vd-dehn-bounded-by-standard-square-word-area`,
`δ_(V_d)(L) <= C·L + C·L^2 · max_{n <= k_0 + C·L} A_d(n)`. If
`A_d(n) <= P_d(n)` for a polynomial `P_d`, which is
`vd-standard-square-words-have-polynomial-area`, then `δ_(V_d)` is bounded by
the polynomial `C·L + C·L^2·P_d(k_0 + C·L)`. That holds for every `d >= 2`, in
particular `d = 10`.
