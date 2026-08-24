---
rg: 2
id: glue-lemma-quadratic-case-proof
kind: route
title: Take the influential coordinates as the list and count them against the influence budget
target: glue-lemma-holds-for-quadratic-functions
requires: []
---

Let `deg f <= 2`, `g = T_rho f`, and let `C_b = q_b + <b>` be
`(d, delta)`-heavy for `g|_{D_b}`.  Noise preserves degree, so
`deg g <= 2` and `(T1)` of
`restricted-influence-transfer-holds-below-degree-three` applies with the
constant `2^d <= 4`:

```text
delta <= Inf^{<=d}_{C_b}(g|_{D_b}) <= 4 * ( Inf_{q_b}(g) + Inf_{q_b + b}(g) ).
```

Hence `max( Inf_{q_b}(g), Inf_{q_b+b}(g) ) >= delta/8`, so at least one of
the two points of `C_b` lies in

```text
Q = { x in Omega : Inf_x(g) >= delta/8 },
```

i.e. `C_b intersect Q != empty`.  This holds for every `b in B`, so
`gamma = 1`.

For the size of `Q`: since `|f| <= 1` we have `||g||_2 <= ||f||_2 <= 1`, and
with `deg g <= 2`

```text
sum_{x} Inf_x(g) = sum_S |S| * hat g(S)^2 <= 2 * ||g||_2^2 <= 2,
```

so at most `2 / (delta/8) = 16/delta` coordinates reach the threshold:
`|Q| <= 16/delta =: L`.

Neither bound mentions `rho`, `d`, `alpha` or `k`, and the density
hypothesis on `B` was never used -- `B` is arbitrary.  Nor was any escape
clause needed: `Q` is produced outright, and it happens to be the set of
ambient influential coordinates, so at ambient degree two the naive decoder
of `glue-lemma-via-ambient-influence-transfer` is correct.  What
`restricted-influence-transfer-holds-below-degree-three` adds is that this
is sharp: the same decoder fails at ambient degree three.
