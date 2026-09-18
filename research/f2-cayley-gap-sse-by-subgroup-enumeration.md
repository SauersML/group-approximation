---
rg: 2
id: f2-cayley-gap-sse-by-subgroup-enumeration
kind: route
title: If subgroups of equal size are F(eta)-near-optimal non-expanding sets in F_2^k Cayley graphs with F independent of delta, enumerating the N^c index-2^c subgroups decides Gap-SSE(eta_0, 2^-c) for any eta_0 with F(eta_0) < 1 - eta_0
target: gap-sse-on-f2-cayley-graphs-is-polynomial
requires: [f2-cayley-subgroup-sets-are-constant-factor-optimal]
---

## Why sufficient

Assume the conjecture `C* < infinity`. Its weak form holds with `F(eta) = C* eta`.
Fix `eta_0 = 1/(2 + 2C*)`, so `F(eta_0) = C*/(2 + 2C*) < 1/2 < 1 - eta_0`.

Given `k`, `c` and `w` with total `W`, enumerate every `c`-dimensional subspace
`V` through its reduced row echelon basis. There are at most
`4 * 2^(c(k-c)) <= 4 N^c` of them. For `H = V^perp` compute
`w(F_2^k \ H) = sum_a w_a 1[some basis row v of V has a.v = 1]` in time `O(N c)`.
Accept iff some `H` has `w(F_2^k \ H) <= F(eta_0) W`.

- *YES* (`Phi_G(2^-c) <= eta_0`): some `S` with `|S| = 2^(k-c)` has
  `Phi(S) <= eta_0`. By the assumption some subgroup `H` with `|H| = |S|` has
  `Phi(H) = w(F_2^k \ H)/W <= F(eta_0)`, so the algorithm accepts.
- *NO* (`Phi_G(2^-c) >= 1 - eta_0`): every set of size `2^(k-c)`, including every
  such `H`, has `Phi(H) >= 1 - eta_0 > F(eta_0)`, so the algorithm rejects.

The time is `N^(c + 1) poly(k) = N^(log_2(1/delta) + O(1))`. For the weak form,
pick any `eta_0` with `F(eta_0) < 1 - eta_0`; one exists because `F(eta) -> 0`.
The formulas `Phi(H) = w(F_2^k \ H)/W` and `Phi(S) = sum_a w_a d_S(a)/W` are
item 2 and the setting of `f2-cayley-subgroup-sets-lose-at-most-log-inverse-density`.
