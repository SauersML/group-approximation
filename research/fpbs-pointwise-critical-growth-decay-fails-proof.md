---
rg: 2
id: fpbs-pointwise-critical-growth-decay-fails-proof
kind: route
title: Edge-disjoint diagonal two-path blocks in the geodesic grid of a product of trees, evaluated at the path-counting lower bound for p_c
target: fpbs-pointwise-critical-growth-decay-fails
requires: []
artifacts:
  - experiments/pointwise-critical-decay-2026-09-17/check_block_certificate.py
  - experiments/pointwise-critical-decay-2026-09-17/output.txt
---

Complete written proof. Notation as in the claim. The only computation is exact
rational arithmetic, rechecked by the script.

**Standard imports.**

- **Monotone coupling:** `tau_p(u,v)` is nondecreasing in `p`.
- **Path-counting bound:** if `G` has degree `D`, then `p_c >= 1/(D-1)`. There
  are at most `D (D-1)^(n-1)` self-avoiding paths of length `n` from `o`. If
  `p < 1/(D-1)`, the expected number of open ones tends to `0`, so
  `P_p(o <-> infinity) = 0`.

**Step 1 (growth).** `|S^T_d_j| = d (d-1)^(j-1)` for `j >= 1`, and the product
metric is the `l^1` sum of the tree metrics. So

```text
|S_r| = sum_(k+m=r) |S^(T_a)_k| |S^(T_b)_m|.
```

Put `c = a b / ((a-1)(b-1))`. If `a < b`, then
`(b-1)^r <= |S_r| <= c (b-1)^r sum_(k>=0) ((a-1)/(b-1))^k`. So `gr = b-1`.
The same holds for balls, since `|B_r| <= (r+1) max_(j<=r) |S_j|`.

**Step 2 (geodesic grid).** Fix geodesic rays `o = x_0, x_1, ...` in `T_a` and
`o = y_0, y_1, ...` in `T_b`. Consider the vertices `(x_i, y_j)` for
`0 <= i, j <= k`. Every pair `(x_i,y_j) - (x_(i+1),y_j)` and every pair
`(x_i,y_j) - (x_i,y_(j+1))` is an edge of `G`, because the generating set is the
union of the two factor generating sets.

**Step 3 (blocks).** For `0 <= i < k`, let `E_i` be the event that at least one
of the two length-2 paths below is open:

```text
(x_i,y_i) - (x_(i+1),y_i) - (x_(i+1),y_(i+1))
(x_i,y_i) - (x_i,y_(i+1)) - (x_(i+1),y_(i+1))
```

- The four edges used by block `i` are distinct.
- An edge of block `i` changes the pair of coordinate indices from `(i,i)` to
  `(i+1,i)` or `(i,i+1)`, or from one of those to `(i+1,i+1)`. So the edge sets
  of different blocks are disjoint.
- Hence the `E_i` are independent, and
  `P_p(E_i) = 1 - (1-p^2)^2 = 2p^2 - p^4`.
- On `E_0 ∩ ... ∩ E_(k-1)`, the vertex `o = (x_0,y_0)` is joined to
  `z_k = (x_k,y_k)`.

So `tau_p(o, z_k) >= (2p^2 - p^4)^k` for every `p`.

**Step 4 (criticality).** The degree of `G` is `D = a+b`. The path-counting
bound gives `p0 = 1/(D-1) <= p_c`, and `2p^2 - p^4` is increasing on `[0,1]`.
With monotone coupling,

```text
tau_(p_c)(o,z_k) >= tau_(p0)(o,z_k) >= (2 p0^2 - p0^4)^k.
```

Since `|z_k| = 2k` and `gr = b-1`,

```text
tau_(p_c)(o,z_k) gr^(|z_k|) >= R^k,   R = (b-1)^2 (2 p0^2 - p0^4).
```

**Step 5 (numbers).**

- `T_3 □ T_10`: `p0 = 1/12`, `2p0^2 - p0^4 = 287/20736`, and `R = 81·287/20736 = 287/256`.
- `T_4 □ T_12`: `p0 = 1/15`, and `R = 121·449/50625 = 54329/50625`.
- `T_2 □ T_6`: `p0 = 1/7`, and `R = 25·97/2401 = 2425/2401`.

All three exceed `1`, so `R^k -> infinity`.

**Weak form.** Suppose `tau_(p_c)(o,x) <= C gr^(-(1-eps)|x|)`. Then
`R^k <= C gr^(2 eps k)` for all `k`, so `log R <= 2 eps log gr`. For
`T_3 □ T_10` this means `eps >= log(287/256)/(2 log 9) ≈ 0.026`.

**Remark (what is not claimed).** Step 4 uses only the crude bound `p0 <= p_c`.
A better lower bound for `p_c` enlarges the violating range. The claim says
nothing about the sphere sum `M_r(p_c)`. On `T_3 □ T_10` there are about
`18^k` diagonal points, so Step 4 gives only a diagonal contribution of order
`(18·287/20736)^k ≈ 0.249^k` to `M_(2k)`. That does not contradict EG0.
