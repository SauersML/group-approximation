---
rg: 2
id: tall-cylinder-seams-reglue-within-quadratic-profile-proof
kind: route
target: tall-cylinder-seams-reglue-within-quadratic-profile
title: Proof that locally tall cylinder decompositions reglue within 96 rho^2 + 20 rho sum w_j/tau_j, and that the ratio term is needed when b is kept
requires:
  - excised-square-kills-cone-local-slit-pair-repair
---

**Conventions.** `(b, c)` are permutations of a finite set `X`. For `s, t >= 1` put
`N(s, t) = #{y in X : c^t b^s y != b^s c^t y}`. The commutator `P = b^s c^t b^(-s) c^(-t)` moves `x = c^t b^s y`
exactly when `y` is counted in `N(s, t)`, so `N(s, t)` is the number of points moved by `P`. A permutation moving
`k` points has `rank(P - I) >= k/2`, since each cycle of length `l >= 2` contributes `l - 1 >= l/2`. Hence

`(0)  N(s, t) <= 2 rank([b^s, c^t] - I) <= 2 rho (s + t)`, where `rho = Lambda_rect(b, c)`.

Also `N(s, -t) := #{y : c^(-t) b^s y != b^s c^(-t) y} = N(s, t)`: put `y = c^t y'`, then
`c^(-t) b^s c^t y' = b^s y'` is equivalent to `b^s c^t y' = c^t b^s y'`.

For permutations, `rank(c' - c) <= #{x : c'(x) != c(x)}`. All costs below count points.

**1. Cylinders and seams.** Rows are `b`-cycles. Say `c` is *equivariant on a row* `r` if `c b = b c` on `r`. Then
`c(r)` is a row of the same length, and `c|_r` is a rotation onto it. Each row has at most one row mapped onto it
equivariantly (by bijectivity of `c`). So the relation "`c` maps `r` equivariantly onto `r'`" splits the rows into
maximal chains, which are paths or cycles. A cycle is a flat torus component on which `b` and `c` commute. A path
`r_1, ..., r_h` is a cylinder `C` of width `w = |r_1|` and height `h`. Its rows are identified with `Z/w` so that
`c(j, y, x) = (j, y + 1, x)` for `y < h - 1`; the top row is `y = h - 1`. Since the chain is maximal, `c` is not
equivariant on the top row. Let `C_1, ..., C_m` be the cylinders, `w_j`, `h_j` their widths and heights. The seam is
`sigma(j, x) = c(j, h_j - 1, x) = (beta(j, x), 0, sigma_x(j, x))`, a bijection from the top points onto the bottom
points (bottom rows are exactly the rows not equivariant images, which are the bottoms of the paths).

A *break* is a top point `z = (j, x)` with `c b z != b c z`, that is `sigma(j, x+1) != sigma(j, x) + 1` (the `+1` in
the target row). Every top row contains a break, and every break is counted in `N(1, 1)`. So

`(1)  m <= N(1, 1) <= 4 rho.`

For a top point `z = (j, x)` set `tau_j = min(h_j, h_beta for all beta that meet the top or the bottom of C_j under
the seam)`.

**2. Single crossings.** Fix `j`, `1 <= t <= tau_j`, and a top point `z = (j, x)`. The `t` points
`x_y = (j, y, x)` with `h_j - t <= y <= h_j - 1` satisfy `c^t x_y = (beta(z), y', sigma_x(z))`, where
`y' = t - (h_j - y) <= t - 1 < h_beta(z)`. Indeed the orbit climbs to the top, crosses the seam once, and then climbs
`y' < h_beta` rows inside `C_beta(z)`, where `c` acts as the identity on the column index. Likewise, for a bottom
point `z' = (beta, 0, x')` with `sigma^(-1)(z') = (j, x)` and `1 <= t <= tau_beta`, the `t` points
`(beta, y, x')`, `0 <= y <= t - 1`, have `c^(-t)` in `C_j` in column `x`. In both cases the column is carried by
`sigma` (or `sigma^(-1)`), and `b` acts on each row as the rotation `x -> x + 1` of its own cylinder.

**3. Width lemma.** Let `u_j = #{x in Z/w_j : w_beta(j,x) does not divide w_j}`. Take `s = w_j` and `t = tau_j`.
For `y` in the column over such an `x` with height at least `h_j - t`, `b^s y = y`, so `c^t b^s y = c^t y`. But
`c^t y` lies in `C_beta` with `w_beta` not dividing `s`, so `b^s c^t y != c^t y`. These `t u_j` points are distinct.
By `(0)`,

`(2)  tau_j u_j <= N(w_j, tau_j) <= 2 rho (w_j + tau_j)`, so `u_j <= 2 rho (1 + w_j / tau_j)`.

From the bottom side, with `c^(-t)` and `N(s, -t) = N(s, t)`, the number `u'_beta` of bottom points of `C_beta` whose
source top has width not dividing `w_beta` satisfies `u'_beta <= 2 rho (1 + w_beta / tau_beta)`. A seam point whose
two cylinders have different widths fails divisibility in at least one direction. So the set `U` of seam points
joining different widths has

`(3)  |U| <= sum_j u_j + sum_beta u'_beta <= 2 rho (2m + 2 sum_j w_j / tau_j).`

**4. Offset lemma.** Fix `j`, write `w = w_j`, and let `V_j` be the top points `x` of `C_j` with `w_beta(j,x) = w`. Give
`x in V_j` the *class* `(beta(j, x), sigma_x(j, x) - x mod w)`. For `0 <= s < w` and `x in V_j`, the relation
`sigma(j, x + s) = sigma(j, x) + s` holds exactly when `x + s` lies in `V_j` in the same class. If it fails and
`1 <= s`, then with `t = tau_j` the `t` points over `x` of height at least `h_j - t` are counted in `N(s, t)`: by
Section 2, `c^t b^s y` sits in column `sigma_x(j, x + s)` of `C_beta(j,x+s)` and `b^s c^t y` in column
`sigma_x(j, x) + s` of `C_beta(j,x)`, at the same height. Summing over `s` and using `(0)`,

`t sum_(x in V_j) (w - n(x)) <= sum_(s=1)^(w-1) N(s, t) <= 2 rho (w^2/2 + w t)`,

where `n(x)` is the size of the class of `x`. With `m*_j` the largest class size, `n(x) <= m*_j`, so
`|V_j| (w - m*_j) <= rho w (w/tau_j + 2)`. Therefore

`(4)  w_j - m*_j <= 2 rho (2 + w_j / tau_j)` if `|V_j| >= w_j/2`, and `w_j - m*_j <= w_j < 2 |U cap top_j|` otherwise.

**5. Regluing.** Call `j` *majority* if `m*_j > w_j/2`, with class `(beta_j, a_j)`. Two majority tops `j != j'` have
`beta_j != beta_j'`: otherwise `sigma` would inject `m*_j + m*_j' > w_beta` points into the bottom row of `C_beta`.
Define `c'` on the top row of a majority `j` by `c'(j, h_j - 1, x) = (beta_j, 0, x + a_j)`. It differs from `c` on
`w_j - m*_j` points. For each width `w`, the numbers of tops and of bottoms of width `w` are equal (both count the
cylinders of width `w`). The majority assignment is injective and width-preserving, so the remaining tops of width
`w` can be matched bijectively to the remaining bottoms of width `w`; glue each by any rotation. A non-majority top
costs at most `w_j <= 2 (w_j - m*_j)`. The new `c'` is a bijection, equals `c` off the top rows, and is equivariant on
every row. So `c' b = b c'`, and

`cost <= 2 sum_j (w_j - m*_j) <= 2 [ sum_j 2 rho (2 + w_j/tau_j) + 2 |U| ]`, by `(4)`,
`<= 8 rho m + 4 rho S + 8 rho (2m + 2 S) = 24 rho m + 20 rho S`, where `S = sum_j w_j / tau_j`, by `(3)`,
`<= 96 rho^2 + 20 rho S`, by `(1)`.

Trivially `cost <= sum_j w_j` too (glue every top by the width-preserving bijection that maps each cylinder to
itself). If every `w_j <= tau_j`, then `S <= m <= 4 rho` and `cost <= 176 rho^2`. This proves Theorem 1. The vertical
statement follows by exchanging the roles of `b` and `c` (the profile is symmetric up to inversion, and
`N(s, -t) = N(s, t)`).

**6. Theorem 2.** In `T_n` the rows are `1, ..., n-1` (length `n`) and row `0` (length `n - 1`, the hole at `(0,0)`
removed). `c` is equivariant on rows `1, ..., n-2`, so `A` = rows `1, ..., n-1` is a cylinder with `h_A = n - 1`.
Row `0` is a cylinder `B` with `h_B = 1`, since `c` maps it into row 1 in columns `1, ..., n-1`, which is not a whole
row. Let `c'` commute with `b`. Then `c'` maps each `b`-cycle onto a `b`-cycle of the same length. Row `0` is the
only cycle of length `n - 1`, so `c'(row 0) = row 0`. But `c(row 0)` lies in row 1, so `c' != c` on all `n - 1`
points of row 0. And `c` maps the `n - 1` points `(x, n-1)`, `x != 0`, of row `n - 1` into row 0, whereas `c'` maps
nothing outside row 0 into row 0. So `c' != c` there too, and the cost is at least `2(n-1)`. Both counts are exact
for `3 <= n <= 9` (`seams.py`). Meanwhile `rho(T_n) <= 2` by `excised-square-kills-cone-local-slit-pair-repair`, and
`T_n` is at distance 1 from a torus once `b` may change too (pad one square into the hole). Here
`w_B/tau_B = n - 1`, so the term `20 rho S` of Theorem 1 cannot be replaced by any `f(rho)` for regluings with
`b' = b`. □

**7. Theorem 3 (height gap).** Let `j != beta` be cylinders with `w_beta != w_j`, let `a = a_(j beta)` be the number
of top points of `C_j` that the seam sends to the bottom of `C_beta`, and put `t = min(h_j, h_beta)`. Then

`(5)  a t <= N(s, t) <= 2 rho (max(w_j, w_beta) + t)`, so `t <= 2 rho max(w_j, w_beta) / (a - 2 rho)` when `a > 2 rho`.

Here `s = w_j` if `w_beta` does not divide `w_j`, and `s = w_beta` otherwise.

*Proof.* Suppose first that `w_beta` does not divide `w_j`. For each of the `a` top points `z = (j, x)` with
`beta(z) = beta`, take the `t` points `(j, y, x)` with `h_j - t <= y <= h_j - 1`. As in Section 2 (the argument uses
only `t <= h_j` and `t <= h_beta`), `c^t` carries them into `C_beta` after one seam crossing. Since `b^s` fixes `C_j`
pointwise and moves every point of `C_beta` (as `w_beta` does not divide `s`), each of them is counted in `N(s, t)`.

Otherwise `w_beta` divides `w_j`, so `w_beta < w_j` and `w_j` does not divide `w_beta`. Use the `a` bottom points
`(beta, 0, x')` whose seam preimage lies in `C_j`, and the points `(beta, y, x')` with `0 <= y <= t - 1`. The map
`c^(-t)` carries them into `C_j`, `b^s` fixes `C_beta`, and it moves `C_j`. So they are counted in
`N(s, -t) = N(s, t)`.

In both cases the `a t` points are distinct, and `(0)` gives `(5)`. □

This is the height side of the dichotomy in the brief. Suppose a seam joins two different widths along a set of mass
`a >= max(w_j, w_beta)/2 >= 4 rho`. Then `min(h_j, h_beta) <= 8 rho`. So a large width mismatch forces one of the two
cylinders to be *short*, with height `O(rho)`,, not just shorter than its width.

**Remarks.**
- The only place where local tallness enters is the time window `t = tau_j` of Section 2, which makes every counted
  orbit cross exactly one seam. Without it, `c^t` composes several seams, as for `T_n`.
- The proof never uses cone points or short loops, so it is independent of the self-bound dichotomy. On the tall
  class it gives the repair in a single step.
