---
rg: 2
id: puncture-triples-defeat-partition-coarsening-proof
kind: route
title: Distinct multipliers force the all-zero labeling, and two transpositions at label 0 cost it alpha while honest random labels pay only 2 alpha p^-l
target: puncture-triples-defeat-partition-coarsening
requires: []
artifacts:
  - experiments/puncture-triples-2026-09-17/check_puncture_triples.py
---

Notation as in the target. Put `P = {0, 1}`, the two labels moved by `pi`.

## Item 1 (completeness)

On edge `i`, a uniform `h in H_i` has `h_a = x` uniform on `F_(p^l)` and
`h_b = lambda_i x`, which is also uniform because `lambda_i != 0`. Honest labels
are `F(w_a) = x`, `F(w_b) = lambda_i x`. The cross triple always accepts. The
triple `(w_a, w_a, pi)` accepts iff `pi(x) = x`, iff `x notin P`, so it rejects
with probability `|P| / p^l = 2 p^(-l)`. The same holds for `(w_b, w_b, pi)`. Hence
the rejection probability on every edge is
`(alpha/2)(2 p^(-l)) + (alpha/2)(2 p^(-l)) = 2 alpha p^(-l)`, and the oblivious
completeness is `1 - 2 alpha p^(-l)`. At `h = 0` both same-owner triples reject,
so the pointwise rejection is `alpha`.

## Item 2 (value of `V`)

Write `F(w_a) = u`, `F(w_b) = v`. The acceptance probability is

```text
acc(u, v) = (1 - alpha) * |{ i : lambda_i u = v }| / r
            + (alpha/2) * ( [u notin P] + [v notin P] ).
```

*Upper bound.* If `u = 0`, then `lambda_i u = 0`. So the cross count is `r` if
`v = 0` and `0` otherwise, and `acc <= max(1 - alpha, alpha/2) = 1 - alpha`,
because `alpha < 1/2` gives `alpha/2 < 1 - alpha`. If `u != 0`, the elements
`lambda_i u` are distinct, so at most one `i` has `lambda_i u = v`, and
`acc <= (1 - alpha)/r + alpha`. Hence
`val(V) <= max(1 - alpha, (1 - alpha)/r + alpha)`.

*Attainment.* `u = v = 0` gives `1 - alpha`. For the other branch pick `u notin P`,
which exists since `p^l >= 4`. At most one `i` has `lambda_i u = 1`, and `r >= 2`,
so some `i` has `v = lambda_i u notin P`. Indeed `lambda_i u != 0` because
`u != 0`. This gives `(1 - alpha)/r + alpha`.

*Value.* With `alpha = (r-1)/(2r-1)`, `1 - alpha = r/(2r-1)` and
`(1 - alpha)/r + alpha = (1 + r - 1)/(2r-1) = r/(2r-1)`. So
`val(V(Phi)) = r/(2r-1)`. (This choice of `alpha` balances the two branches; any
`0 < alpha < 1/2` already gives `val(V) = max(1 - alpha, (1-alpha)/r + alpha) < 1`.)

## Item 3 (coarsening and twin)

Identity views have singleton level-set partitions. The cross triples are exact,
since `h_b = lambda_i h_a` on all of `H_i`, and they induce `beta_i = lambda_i`. The
same-owner triples with `pi` reject `h_a in P`, so they are not exact. Therefore
`Can_part(Phi, V)` is the game on `(a, singletons)` and `(b, singletons)` with the
`r` constraints `v = lambda_i u` of weight `1/r` each. The labeling `u = v = 0`
satisfies all of them, so `val(Can_part) = 1`. In `V^0` the same-owner triples
accept every labeling, and `u = v = 0` satisfies the cross triples, so
`val(V^0) = 1`.

## Consequence for the refuted claim

`low-degree-view-collapse-survives-non-affine-sigma` asserts
`val(V(Phi)) >= (1 - o(1)) val(Can_part(Phi, V)) - o(1)` with `o(1) -> 0` as
`eps -> 0` at fixed `p, gamma`, for views of degree `d <= (1-gamma) log_p(1/eps)`
and arbitrary `sigma`. Take `gamma = 1/2`, fix `r = 2` and let `l -> infinity`.
Then `eps = (2/3) p^(-l) -> 0`, and `log_p(1/eps) >= l > 2 = d/(1-gamma)` for
`l >= 3`. The right side tends to `1`, but `val(V) = 2/3` for every `l`. The
claim is false.

## Replay

`experiments/puncture-triples-2026-09-17/check_puncture_triples.py`, part (CX),
brute-forces all labelings for `(p, l, r)` in `(2,2,2), (2,3,2), (2,3,3),
(2,4,2), (2,4,3), (2,5,4), (3,2,2), (3,2,3), (5,2,3)`, building `F_(p^l)` from an
irreducible polynomial found by search. It confirms `val(V) = r/(2r-1)`,
`val(Can_part) = val(V^0) = 1`, the oblivious rejection `2 alpha p^(-l)` and the
pointwise rejection `alpha`. The script reports 0 failures on seeds `20260917`
and `7`.
