---
rg: 2
id: no-heisenberg-from-linear-depth-growth
kind: route
title: A Heisenberg center has sublinear depth growth, so linear depth growth of every infinite-order unit excludes H_3(Z) from the binary Leavitt unit group
target: leavitt-unit-group-has-no-integer-heisenberg-subgroup
requires: [leavitt-units-of-infinite-order-have-linear-depth-growth]
---

Let `R = L_(F_2)(1,2)`, `Q = R^x`, `R_N = span{ S[alpha]T[beta] : |alpha|, |beta| <= N }`,
`ell(x) = min{ N : x in R_N }`, and for a unit `u` put
`D_u(m) = max(ell(u^m), ell(u^-m))` and `lambda(u) = lim_m D_u(m)/m`.

1. `R_N R_M <= R_(N+M)`, so `ell(xy) <= ell(x) + ell(y)`. This is step 1 of
   `thompson-elements-are-undistorted-in-leavitt-unit-group-proof`.
2. Suppose `a, b` in `Q` and `c = [a,b]` commutes with `a` and `b` and has infinite order.
   In the group `<a,b>` one has `[a^m, b^m] = c^(m^2)` for all `m >= 1`, and
   `[a^m, b^m]^(-1) = [b^m, a^m] = c^(-m^2)`.
3. By step 1, `ell(c^(+-m^2)) <= m (ell(a) + ell(a^-1) + ell(b) + ell(b^-1))`. So
   `D_c(m^2) <= K m` with `K` independent of `m`, and `lambda(c) = lim D_c(m^2)/m^2 = 0`.
4. `leavitt-units-of-infinite-order-have-linear-depth-growth` says `lambda(c) > 0`.
   This contradicts step 3, so no such `a, b` exist.
5. A subgroup of `Q` isomorphic to `H_3(Z)` gives such `a, b` (its standard generators),
   so `Q` has no subgroup isomorphic to `H_3(Z)`. ∎

The same computation with `t x t^-1 = x^k`, `|k| >= 2`, gives
`D_x(|k|^j) <= 2j (ell(t) + ell(t^-1)) + D_x(1)` and `lambda(x) = 0`, so the premise also
excludes every `BS(1,k)` with `|k| >= 2`.
