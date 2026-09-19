---
rg: 2
id: hermitian-edge-trace-norm-web-k4-small-window-limits-proof
kind: route
title: Bound every packing by n times the largest window density, and bound the density of each of the 91 induced subgraphs of at most six vertices by an explicit admissible matrix
target: hermitian-edge-trace-norm-web-k4-small-window-limits
requires: []
artifacts:
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/README.md
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/cover.py
  - experiments/hermitian-edge-trace-norm-web-k4-p7-2026-09-19/cover6.log
---

An ordinary proof with a finite floating-point check. It is unreviewed and not Lean-verified.
Lane w10-078, 2026-09-19.

## Step 1. A packing bound is at most `n` times the best density

Let `y_W >= 0` satisfy `sum_{W ni i} y_W <= 1` for every vertex `i` of `C_n^4`. Let `d` be the
largest density `c(G[W]) / |W|` over the sets `W` with `y_W > 0`. Then

```text
sum_W y_W c(G[W])  <=  d sum_W y_W |W|  =  d sum_i sum_{W ni i} y_W  <=  d n .
```

So if `d n < R_n = sqrt3 (n - floor(n/5))`, the right side of (P) is below `R_n`.

## Step 2. Upper bounds on `c(G[W])`

Any admissible `C_W` on `G[W]` gives `c(G[W]) <= ||C_W||_1`. The density depends only on the
isomorphism type of `G[W]`.

**Enumeration.** `cover.py` lists every vertex set `W` that contains `0` and has `|W| <= 6`, in
each of `C_13^4`, `C_14^4` and `C_19^4`. Every set is a rotation of such a set. It sorts the
induced graphs into isomorphism classes with networkx. There are `91` classes, of which
`1, 2, 4, 9, 21, 54` have sizes `1, ..., 6`.

**Upper bound for each class.**

1. It minimises `||C||_1` over moduli `1 + x^2` and free phases (4 random starts, then BFGS and
   Nelder-Mead).
2. It rescales so that every edge modulus is at least `1`, and asserts that the result is
   admissible.
3. It records the trace norm of that explicit matrix.

**The densities.** By `cover6.log`, the largest density is `1.46844`. It is that of `G_6`
(`c(G_6) <= 8.81064`). The next is `1.44805`, from `K_5` (`c(K_5) <= 7.24025`; the true value is
about `5 + sqrt5 = 7.2361`). Every other class has density at most `1.44022`. The densities needed
are `R_n / n`:

| `n` | `R_n` | `R_n / n` | best density allowed | margin |
|---|---|---|---|---|
| 13 | `11 sqrt3 = 19.0526` | `1.46558` | `1.44805` (without `G_6`) | `0.0175` |
| 14 | `12 sqrt3 = 20.7846` | `1.48461` | `1.46844` | `0.0162` |
| 19 | `16 sqrt3 = 27.7128` | `1.45857` | `1.44805` (without `G_6`) | `0.0105` |

Floating-point error in a Hermitian eigenvalue computation of size at most `6` is below `1e-12`.
That is far below these margins.

## Step 3. Conclusion

By Steps 1 and 2, `d n < R_n` in each of the three cases. This proves (a) and (b).

**Sufficiency of `G_6`.** The `n` rotations of `W_0 = {0, 1, 2, 3, 4, 6}` with weight `1/6` cover
each vertex exactly `6` times. They therefore form a valid packing, and they give
`||C||_1 >= (n/6) c(G_6)`.

**Pinching.** Pinching into a partition, `||C||_1 >= sum_i ||C_{W_i}||_1`, is the special case
`y = 1` on the parts.

- Pinching `P_7^4` into parts of at most six vertices gives at most
  `7 x 1.46844 = 10.279 < 6 sqrt3 = 10.3923`.
- So `c(P_7^4) >= 6 sqrt3` cannot be proved from smaller pieces this way.
