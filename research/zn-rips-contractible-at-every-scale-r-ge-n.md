---
rg: 2
id: zn-rips-contractible-at-every-scale-r-ge-n
kind: claim
title: "Zaremsky's conjecture: the Rips complex of Z^n in the l^1 metric is contractible at every scale r ≥ n"
distinct_from:
  zaremsky-4-03-rips-complex-of-zn-contractible: that is Zaremsky's Problem 4.3, contractibility for all large enough scales, answered by Virk; this is the sharp form, every scale r ≥ n
  rips-complexes-of-integer-lattices-are-contractible: that is Virk's theorem for r ≥ n^2(2n−1); this asks for every r ≥ n
---

For every `n ≥ 1` and every integer `r ≥ n`, the Vietoris–Rips complex `VR(Z^n, d_1; r)` is contractible. A finite
set spans a simplex iff its `l^1` diameter is at most `r`.

Here `d_1` is the standard word metric. Large-scale contractibility is Virk's theorem (`rips-complexes-of-integer-lattices-are-contractible`).
This claim asks for the sharp threshold.

Status on main, by dimension:
- `n ≤ 6`: every `r ≥ n`. This is Gupta–Sarkar–Shukla together with `z6-rips-contractible-at-scales-6-to-9`.
- `n = 7`: every `r ≥ n` except `r = 11, 13, 15, 17`. The sources are:
  - `z7-rips-contractible-at-scales-7-and-8`;
  - `z7-rips-contractible-at-scale-9`;
  - `z7-rips-contractible-at-scale-10`;
  - `z7-rips-contractible-at-scales-12-14-16-and-18-to-54`;
  - `z7-rips-contractible-at-scales-20-to-54-even-and-36-to-54`;
  - Zaremsky's bound `r ≥ 55`.
- `n = 8`: every `r ≥ 37` and every even `r ≥ 20`. The sources are
  `z8-rips-contractible-at-scales-20-to-36-even-and-37-to-70` and `z8-rips-contractible-at-even-scales-38-to-70`,
  with the published bound `r ≥ 71`. Open: `8 ≤ r ≤ 19` and odd `21 ≤ r ≤ 35`.
- General `n`, sufficient criteria on the partitions of `r`: `zn-rips-sphere-balanced-dominator-criterion` and
  `zn-rips-slack-sphere-criterion`.

## Attempts

- **w3-103, partition criteria.** The balanced-dominator and slack-one sphere criteria handle each scale where every
  unbalanced partition of `r` into at most `n` parts has exactly `n` parts. They stall when some unbalanced partition
  has fewer than `n` parts: the stuck sphere points then have a zero coordinate. For `n = 7` this happens at
  `r = 10, 11, 13, 15, 17`.
- **w5-103, lifted interleaved certificates.** The reduction is in `z7-rips-contractible-at-scale-10-proof`.
  - *Lift.* A peeling link lives in the dimension `k` of its last positive box side, so `e_k` is always available
    as a dominator direction. There is one certificate per `k ≤ n`, and each ends at `{e_k}`.
  - *Interleaving.* Norm `r − 1, …, 2` points are deleted against the remaining sphere.
  - *Cone collapse.* A link is collapsed to a cone with the moves `hull(0, u, b, e_k)`.

  Result: `(7, 10)` is closed.
  - In exploratory runs without the lift, the greedy stalls at `(6,6)`, `(7,7)`, `(7,8)` and `(7,10)`.
  - Point-level certificates grow quickly: `|Lmax_7|` is 216,952 at `r = 10` and 397,727 at `r = 11`, and far larger
    at `(7,17)` and at `n = 8`. The remaining scales need either staged runs or a partition-level version of the lifted
    moves.
