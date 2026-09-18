---
rg: 2
id: hermitian-edge-trace-norm-clique-inequality-large-m-proof
kind: route
title: Einollahzadeh's modulus lemma and a Schur product make one spectral part rank one; AM-GM averaging and a Yudin-type LP certificate on the complex sphere then give the clique inequality for m >= 6
target: hermitian-edge-trace-norm-clique-inequality-large-m
requires: []
artifacts:
  - experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/verify.py
  - experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/verify_F_m6_D4.log
  - experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/README.md
---

This is an ordinary proof plus one computer-verified polynomial inequality (Lemma 4). It is
unreviewed and not Lean-verified. Lane w6-078, 2026-09-18. Scripts and logs are in
`experiments/hermitian-edge-trace-norm-clique-energy-2026-09-18/`.

**Theorem.** Let `m >= 6` and let `C` be Hermitian `m x m` with `C_ii = 0` and `|C_ij| >= 1`
(`i != j`). Then `||C||_1 >= sqrt3 (m-1)`.

## Step 1. Rank-one reduction

Write `C = A - B` with `A = C_+`, `B = C_-`. Both are PSD. Since `C_ii = 0`, they have equal
diagonals `A_ii = B_ii =: d_i`, and `||C||_1 = tr A + tr B = 2 sum_i d_i`. Every `d_i > 0`. If
`d_i = 0`, then row `i` of both PSD matrices vanishes, so `C_ij = 0`, contrary to `|C_ij| >= 1`.

**Lemma 1 (Einollahzadeh, arXiv:2309.14958, Lemma clem1).** If `a, b in C`, `delta > 0` and
`|a|, |b| <= delta`, then `|a - b| <= |delta - conj(a) b / delta|`.

*Proof.* Expanding both squares,
`|delta - conj(a)b/delta|^2 - |a-b|^2 = delta^2 - |a|^2 - |b|^2 + |a|^2|b|^2/delta^2
= (delta^2 - |a|^2)(delta^2 - |b|^2)/delta^2 >= 0`. ∎

Put `X = diag(d_i^{-1/2})` and define

```text
N  :=  X ( conj(A) o B ) X ,     N_ij = conj(A_ij) B_ij / sqrt(d_i d_j) .
```

`conj(A) = A^T` is PSD, so the Schur product `conj(A) o B` is PSD and hence so is `N`. Also
`N_ii = d_i`. Therefore `G_ij := N_ij / sqrt(d_i d_j)` is a PSD matrix with unit diagonal, i.e. the
Gram matrix of unit vectors, and `|G_ij| <= 1`. The `2 x 2` minors give `|A_ij|, |B_ij| <= sqrt(d_i d_j)`.
So Lemma 1 with `delta = sqrt(d_i d_j)` gives, for all `i != j`,

```text
(R1)     1  <=  |C_ij|  =  |A_ij - B_ij|  <=  | sqrt(d_i d_j) - N_ij |  =  sqrt(d_i d_j) |1 - G_ij| .
```

In particular `G_ij != 1`.

**Corollary 1' (strict reduction of UCI).** `K := sqrt(d) sqrt(d)^T - N` has zero diagonal and
`|K_ij| >= 1`. It has at most one positive eigenvalue, and `||K||_1 = 2 lambda_+(K) <= 2 sum d = ||C||_1`.
Hence (UCI) for size `m` is equivalent to the case where the matrix has exactly one positive
eigenvalue, and to the statement "(R1) implies `sum d >= (sqrt3/2)(m-1)`".

## Step 2. Averaging

Each `i` lies in `m - 1` pairs. By AM-GM and (R1),

```text
sum_i d_i = (1/(m-1)) sum_{i<j} (d_i + d_j)  >=  (2/(m-1)) sum_{i<j} sqrt(d_i d_j)
          >=  (1/(m-1)) E(G),        E(G) := sum_{i != j} 1/|1 - G_ij| .
```

(Note `|1 - G_ji| = |1 - G_ij|`.) Hence `||C||_1 >= 2 E(G)/(m-1)`. It suffices to show

```text
(E_m)     E(G)  >=  (sqrt3/2) (m-1)^2     for every PSD G with unit diagonal and G_ij != 1 (i != j).
```

*Remark (the exact form).* The same AM-GM with any fractional perfect matching `y` of `K_m` in
place of the uniform `y_ij = 1/(m-1)` gives `sum d >= 2 nu_f(r)`, where `r_ij = 1/|1 - G_ij|` and
`nu_f` is the maximum `r`-weight of a fractional perfect matching. Step 2 uses the barycenter of the
matching polytope.

## Step 3. A linear programming bound on the complex sphere

**Lemma 3.** Let `F(z) = sum_{0 <= p,q <= D} c_pq z^p zbar^q` with real `c_pq = c_qp`, and
`c_pq >= 0` for `(p,q) != (0,0)` (`c_00` of any sign). Then `F` is real-valued. For every
`m x m` PSD `G` with unit diagonal, `sum_{i,j} F(G_ij) >= c_00 m^2`. If moreover
`F(z) <= 1/|1-z|` for all `|z| <= 1`, `z != 1`, then

```text
E(G)  >=  c_00 m^2  -  m F(1) .
```

*Proof.* `conj(F(z)) = sum c_pq zbar^p z^q = F(z)` by symmetry. The matrix
`[G_ij^p conj(G_ij)^q] = G^{op} o conj(G)^{oq}` is a Schur product of PSD matrices, so its entry sum
is `>= 0`. The `(0,0)` term contributes `c_00 m^2`. Then `|G_ij| <= 1` and
`E(G) >= sum_{i != j} F(G_ij) = sum_{i,j} F(G_ij) - m F(1)`. ∎

## Step 4. The certificate

Take `D = 4` and the seven nonzero coefficients (all others `0`)

```text
c_00 = 4512199/5000000   c_01 = 2845603/10000000   c_02 = 438289/5000000   c_03 = 23667/1250000
c_04 = 3211/500000       c_13 = 9629/400000        c_14 = 5543/312500
```

so that

```text
F(z) = c_00 + 2 c_01 Re z + 2 (c_02 + c_13 |z|^2) Re z^2 + 2 (c_03 + c_14 |z|^2) Re z^3 + 2 c_04 Re z^4 ,
F(1) = 8906037/5000000 = 1.7812074 ,     c_00 = 0.9024398 .
```

**Lemma 4 (computer-verified).** `F(z) <= 1/|1 - z|` for all `|z| <= 1`, `z != 1`.

*Verification* (`verify.py`, log `verify_F_m6_D4.log`). Both sides are invariant under
`z -> zbar`, so it suffices to take `z = r e^{i theta}` with `(r, theta)` in `[0,1] x [0,pi]`. Then
`F = sum c_pq w_pq r^{p+q} cos((q-p) theta)`, with `w = 1` if `p = q` and `w = 2` otherwise, and
`|1-z|^2 = 1 + r^2 - 2 r cos theta`. On each box, an upper bound for `F` and a lower bound for
`1/|1-z|` are computed:
- `r^n` is monotone;
- the range of `cos(k theta)` over an interval is exact, taking interior extrema into account;
- bilinear products are bounded by their corners;
- every computed bound is widened outward by `10^{-12}` relative plus `10^{-14}` absolute.

Boxes are bisected until the lower bound of `1/|1-z|` exceeds the upper bound of `F`. The run
closes all of `[0,1] x [0,pi]` with 151,615 boxes. The inequality is not tight anywhere. The LP
that produced `F` was solved with the right-hand side `(1 - 0.004)/|1-z|`.

## Step 5. Arithmetic

By Steps 2–4, `||C||_1 >= 2 (c_00 m^2 - m F(1))/(m-1)`. It suffices that

```text
Q(m) := c_00 m^2 - m F(1) - (sqrt3/2)(m-1)^2 = (c_00 - sqrt3/2) m^2 + (sqrt3 - F(1)) m - sqrt3/2  >= 0 .
```

Use `1.7320508 < sqrt3 < 1.7320509` (checked by squaring). Then `Q(m) >= a m^2 + b m + c` for
`m >= 0`, where

```text
a = c_00 - 1.7320509/2 = 0.0364144 > 0 ,    b = 1.7320508 - F(1) ,    c = -1.7320509/2 .
```

The minorant satisfies `a·36 + 6b + c >= 0.14995 > 0`, and its derivative at `6` is
`12a + b >= 0.3878 > 0`. So `Q(m) > 0` for all real `m >= 6`. (For comparison, `Q(5) < 0`.) Hence
`||C||_1 >= sqrt3 (m-1)` for every `m >= 6`. ∎

## Sharpness, and why m = 4, 5 need another idea

**The energy LP is sharp.** The table lists the best value of Lemma 3 over degree `D = 4`
(`yudin_D4.log`), the numerical minimum of `E` (`energy_min.log`, BFGS over `C^m` with 30
restarts), and the needed value `(sqrt3/2)(m-1)^2`.

| m | LP bound for `E` | numerical `min E` | needed |
|---|---|---|---|
| 4 | 7.6569 | 7.6569 = 2 + 4 sqrt2 | 7.7942 |
| 5 | 13.7639 | 13.7638 | 13.8564 |
| 6 | 21.888 | 21.928 | 21.651 |
| 8 | 43.923 | 44.149 | 42.435 |

At `m = 4` the minimum of `E` is attained by the 4th roots of unity in `C^1`: two pairs with
`G = -1` and four with `G = +-i`, so `E = 2(2·1/2 + 4/sqrt2)`. At `m = 5` it is attained by the 5th
roots of unity: `E = 10 (1/(2 sin(pi/5)) + 1/(2 sin(2pi/5)))`. So **no argument that goes through the
averaged bound `sum d >= E(G)/(m-1)` can reach `m = 4, 5`.** This is an obstruction for Steps 2–3 at
any degree: the LP value equals the true minimum of `E`.

These configurations are not counterexamples to (UCI). For the square, `d_i = 1/sqrt2` satisfies (R1)
with `sum d = 2 sqrt2 > 3 sqrt3/2`. The loss is in the uniform averaging: the best perfect matching of
the square has `r`-weight `sqrt2` against the average `(1 + 2 sqrt2)/3`.

**The matching form.** By the Remark in Step 2, (UCI) for size `m` follows from

```text
(M_m)     2 nu_f( 1/|1 - G_ij| )  >=  (sqrt3/2)(m-1)     for all unit-diagonal PSD G .
```

For `m = 4`, `nu_f` is the largest `r`-weight of the three perfect matchings. For `m = 5`, it is the
maximum over the 22 vertices of the fractional perfect matching polytope (half 5-cycles, and half
triangles plus an edge). Numerically (`fmatch.py`, `fmatch.log`, SLSQP with 40 restarts), the minimum
of `2 nu_f` is `2.73205 = 1 + sqrt3` for `m = 4` and `3.61803 = (5 + sqrt5)/2` for `m = 5`. These are
exactly half the numerical minima `2 + 2 sqrt3` and `5 + sqrt5` of `||C||_1`. So `(M_4)` and `(M_5)`
lose nothing, and they are the remaining open core of (UCI).

**Sanity check** (`chain_check.py`, log `chain_check.log`). On 3000 random admissible `C` with
`3 <= m <= 8`, (R1) and `||C||_1 >= 2 E(G)/(m-1)` hold to within `4·10^{-15}`.
