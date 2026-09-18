---
rg: 2
id: hermitian-edge-trace-norm-odd-antihole-facets-by-size
kind: route
title: Odd antiholes by size - house and clique coverings for n = 7, 9 and n >= 15, a Delsarte-type kernel LP on the rank-one reduction for n = 13, and n = 11 left to a K5 bound
target: hermitian-edge-trace-norm-odd-antihole-facets
requires:
  - hermitian-edge-trace-norm-odd-antihole-c11
artifacts:
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/README.md
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/graphbb.py
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/house_c7bar.log
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/k4_c9bar.log
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/cert_ah.py
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/verify_ah.py
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/K_n13_D4.json
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/K_n13_D4_exact.json
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/verify_K_n13_D4.log
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/tail_check.py
  - experiments/hermitian-edge-trace-norm-antihole-2026-09-18/tail_check.log
---

A proof with three computer-verified inequalities (Steps 2, 3 and 4). It is unreviewed and not
Lean-verified. Lane w7-078, 2026-09-18. The only input it does not prove is the case `n = 11`
(`hermitian-edge-trace-norm-odd-antihole-c11`).

**Theorem.** Let `n = 2k + 1 >= 7`, `n != 11`, and let `C` be admissible on the odd antihole `C̄_n`.
Then `||C||_1 >= sqrt3 (n - 2)`. With `hermitian-edge-trace-norm-odd-antihole-c11` this holds for
every odd `n >= 7`.

Notation: vertices are `Z_n`. `i ~ j` iff the cyclic distance `s(i, j) = min(|i-j|, n-|i-j|)` is at
least 2. For a graph `F`, `c(F)` is the minimum of `||C||_1` over admissible `C` on `F` (it is attained
by 2x2 compression and compactness), and `c_m = c(K_m)`.

## Step 1. The covering lemma

**Lemma 1.** Let `U_1, ..., U_r` be vertex sets that cover every vertex exactly `lambda` times. Then
`||C||_1 >= (1/lambda) sum_t ||C_{U_t}||_1` for every Hermitian `C`.

*Proof.* Write `C = P - N`, with `P, N >= 0` and `|C| = P + N`. For each `U`,
`C_U = P_U - N_U` with `P_U, N_U >= 0`, so `||C_U||_1 <= tr P_U + tr N_U = sum_{i in U} |C|_ii`.
Summing over `t` gives `sum_t ||C_{U_t}||_1 <= lambda tr|C| = lambda ||C||_1`. ∎

A principal submatrix of an admissible matrix is admissible on the induced subgraph. So
`c(C̄_n) >= (r/lambda) c(F)` whenever the `U_t` induce copies of `F`.

**Cliques.** `U_t = {t, t+2, ..., t+2(k-1)}`, `t in Z_n`, are `n` cliques of size `k`. Consecutive
elements are at distance 2, and the first and last are at distance `n - 2(k-1) = 3`. Each vertex
lies in `k` of them. So

```text
(1)     c(C̄_n)  >=  (n/k) c_k ,   and   c_k >= sqrt3 k (n-2)/n   suffices.
```

## Step 2. n = 7 and n = 9 (exact SDP branch-and-bound)

*n = 7.* The window `U_t = {t, ..., t+4}` induces the complement of the path `P_5`, the house.
The 7 windows cover each vertex 5 times, so `c(C̄_7) >= (7/5) c(house)`. It suffices that
`c(house) >= 25 sqrt3/7 = 6.18590`. `graphbb.py AH7:0,1,2,3,4 6.1859 3.1 3` certifies
`c(house) >= 6.1859` (`house_c7bar.log`: 68 boxes, 2 seconds). Indeed `(7 * 6.1859/25)^2 = 3.0000041 > 3`.
The numerical value is `c(house) = 2 sqrt10 = 6.3246`. (Cliques alone would need `c_3 >= 5 sqrt3 * 3/7`,
which is false: `c_3 = 2 sqrt3`.)

*n = 9.* By (1) with `k = 4`, it suffices that `c_4 >= 28 sqrt3/9 = 5.38860`.
`graphbb.py K4 5.3887 2.7 3` certifies `c_4 >= 5.3887` (`k4_c9bar.log`: 1984 boxes, 39 seconds). Indeed
`(9 * 5.3887/28)^2 = 3.0001085 > 3`. The numerical value is `c_4 = 2 + 2 sqrt3 = 5.464`.

`graphbb.py` is `experiments/hermitian-edge-trace-norm-clique-small-m-2026-09-18/cliquebb.py` with
two changes. It takes any graph, gauging a BFS spanning tree real instead of the star. It has no
symmetry reduction, so the first free phase ranges over `[0, 2pi]`. The certificate scheme is Steps 1–4 of
`hermitian-edge-trace-norm-clique-inequality-k4-proof`:
- moduli above `T` are closed by 2x2 compression (`2T >= TARGET`);
- otherwise a Gaussian-rational `Z` with `-I < Z < I`, checked in exact arithmetic, gives
  `||C||_1 >= tr(ZC)`;
- that bound is edge-separable, and its minimum over a phase box is computed with outward rounding.

## Step 3. n = 13: a Delsarte-type kernel LP on the rank-one reduction

For `n = 13`, (1) would need `c_6 >= 66 sqrt3/13 = 8.7935`. The energy LP of Step 4 gives only
`c_6 >= 8.720`, and UCI gives `5 sqrt3 = 8.660`. So we use the whole graph instead of its cliques.

*Rank-one reduction.* This is Step 1 of `hermitian-edge-trace-norm-clique-inequality-large-m-proof`,
which uses only `C_ii = 0` and, for (R1), `|C_ij| >= 1` on the pairs where it is applied. Let
`C = A - B` with `A = C_+` and `B = C_-`. Then `A_ii = B_ii = d_i`, and `||C||_1 = 2 sum d_i`. Every
`d_i > 0`, because every vertex has an edge. There is a PSD matrix `G` with unit diagonal (a Gram
matrix of unit vectors) such that on every edge

```text
(R1)     1  <=  sqrt(d_i d_j) |1 - G_ij|     (so G_ij != 1).
```

*Averaging over a fractional perfect matching.* Let `y_s >= 0` (`s = 2..k`) with `2 sum_s y_s = 1`,
and put weight `y_{s(i,j)}` on each edge. Every vertex has two neighbours at each distance `s`, so the
weights at each vertex sum to 1. By AM-GM and (R1),

```text
sum_i d_i = sum_{ij edge} y_s (d_i + d_j) >= 2 sum_{ij edge} y_s sqrt(d_i d_j) >= 2 sum_{ij edge} y_s / |1 - G_ij| ,
(2)     ||C||_1  >=  sum_{(i,j) ordered edge} 2 y_{s(i,j)} / |1 - G_ij| .
```

*The kernel.* Take reals `f_pq(s)` for `0 <= p <= q <= D` and `s = 0..k`, and put
`K(s, z) = sum_{p <= q} w_pq f_pq(s) Re(z^p conj(z)^q)` (`w_pp = 1`, `w_pq = 2` for `p < q`). Suppose:
- (K1) for `(p,q) != (0,0)`, the circulant `F_pq = [f_pq(s(i,j))]` is PSD. Equivalently
  `fhat_pq(t) = f_pq(0) + 2 sum_{s=1..k} f_pq(s) cos(2 pi s t/n) >= 0` for `t = 0..k`;
- (K2) `K(1, z) <= 0` for `|z| <= 1` (non-edges);
- (K3) `K(s, z) <= 2 y_s / |1 - z|` for `|z| <= 1`, `z != 1`, `s = 2..k` (edges).

*Claim.* Then `||C||_1 >= n beta`, where
`beta = 2 sum_{s=1..k} f_00(s) - sum_{(p,q) != (0,0)} w_pq f_pq(0)`.

*Proof.* For `(p,q) != (0,0)`, the Schur product `M_pq = F_pq o G^{o p} o conj(G)^{o q}` is PSD
(Schur product theorem). Its entry sum `1^T M_pq 1` is therefore real and `>= 0`. Summing
`w_pq Re(1^T M_pq 1)` over `(p,q) != (0,0)` gives `sum_{i,j} (K(s(i,j), G_ij) - f_00(s(i,j))) >= 0`.
On the diagonal `G_ii = 1` and `s = 0`, so

```text
sum_{i != j} K(s(i,j), G_ij)  >=  sum_{i != j} f_00(s(i,j)) - n sum_{(p,q)!=(0,0)} w_pq f_pq(0)  =  n beta .
```

By (K2) the non-edge terms are `<= 0`, and by (K3) and (2) the edge terms sum to at most `||C||_1`. ∎

*The certificate.* `cert_ah.py 13 4 0.003 0.002` solves the LP in `(y, f)` on a polar grid
(`D = 4`, with slack `eta = 0.003` in (K3) and `eps = 0.002` in (K2)). The LP value is `19.20962`.
`verify_ah.py` then checks the certificate rigorously (`verify_K_n13_D4.log`):
1. It rounds `y` and `f` to multiples of `10^{-7}` as exact rationals and fixes `y_6` so that
   `2 sum y = 1` exactly.
2. It bounds every `fhat_pq(t)` from below in interval arithmetic (mpmath `iv`, 40 digits). Where a
   bound is negative, it raises `f_pq(0)` by a rational amount so that (K1) holds. This only lowers `beta`.
3. It proves (K2) and (K3) by interval branch-and-bound over `(r, theta) in [0,1] x [0, pi]`. That
   range is enough because `K(s, conj z) = K(s, z)`. Every float bound is widened outward by
   `10^{-12}` relative plus `10^{-14}` absolute. It uses 1 box for `s = 1` and about `2 * 10^5` boxes
   for each `s = 2..6`.
4. It computes `n beta = 4802400421/250000000 = 19.209602` exactly and checks
   `(n beta)^2 >= 3 * 11^2`.

So `c(C̄_13) >= 19.2096 > 11 sqrt3 = 19.0526`.

## Step 4. n >= 15 (exact)

Steps 2–4 of `hermitian-edge-trace-norm-clique-inequality-large-m-proof` prove, for every `m >= 2`,
`c_m >= 2 (c_00 m^2 - m F(1))/(m-1)`, with `c_00 = 4512199/5000000` and `F(1) = 8906037/5000000`.
The certified polynomial inequality (Lemma 4 there) does not depend on `m`. By (1), it suffices that

```text
p(k) = 2 (c_00 k - F(1)) (2k+1) - sqrt3 (2k-1)(k-1)  >=  0 .
```

The coefficient of `sqrt3` is negative for `k >= 2`, so replacing `sqrt3` by `s = 17320509/10^7`
(`s^2 > 3`) gives a lower bound `p_s`. `p_s` is a quadratic with leading coefficient `0.14566 > 0`
and vertex at `0.425`, and `p_s(7) = 0.976 > 0`. So `p(k) > 0` for every `k >= 7`. `tail_check.py`
checks all of this in exact rationals (`tail_check.log`). (`p_s(6) < 0`: this route cannot reach
`n = 13`, which is why Step 3 is needed.)

## Step 5. n = 11

By (1) with `k = 5`, `c_5 >= 45 sqrt3/11 = 7.08566` suffices. This is
`hermitian-edge-trace-norm-odd-antihole-c11`. The kernel LP of Step 3 at `n = 11` gives only `15.53`
(`D = 5`), which is `0.9962` of the target `15.5885`.

## Numerics (not part of the proof)

The degree-5 LP values on `Z_n x disc` are:

| n | LP value | needed |
|---|---|---|
| 9 | 11.84 | 12.12 |
| 11 | 15.53 | 15.59 |
| 13 | 19.34 | 19.05 |
| 15 | 23.17 | 22.52 |

Numerical minimisation over `G` of the right side of (2) with uniform `y` reaches only about `0.93`
of the target for every `n` tested. So the kernel is needed, and so is freedom in `y`.
