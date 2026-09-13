---
rg: 2
id: points-of-c3-approximable-by-zero-cycles-proof
kind: route
title: Take the Chow form of Philippon's approximating zero-cycle in P_3; its height controls b, its distance sum controls a, and Delta, then H, make the combination negative
target: points-of-c3-approximable-by-zero-cycles
requires:
  - philippon-zero-cycles-approximate-points-of-p3
---

Fix `B >= 1` and `C >= 0`. Put `x = theta~ / ||theta~||` in `P_3(C)`. Let
`c_3 = 768` and `K = (4 c_3)^3 = 3072^3`. All constants `c_i` below depend
only on `z` and `S_theta`.

**The cycle.** Apply [[philippon-zero-cycles-approximate-points-of-p3]] with
`n = 3` and integers `Delta >= max(3072^4, K B)` and `H >= 1`, chosen at the
end. It gives an irreducible zero-dimensional cycle `Z` over `Q`, with
geometric points `alpha_1..alpha_D`, `D = d(Z) >= 1`, and

```text
log Dist(x, Z)  <=  -K^(-1) (h(Z) Delta + D H).                         (P)
```

**Chow form and height.**
- **Form.** The eliminant form of `Z` of content 1 is
  `F = g = c prod_j (u . alpha~_j)`, with representatives `alpha~_j in Qbar^4`
  and a constant `c`.
- **Height.** With `m` as in the import (sphere integral plus
  `deg . sum_(i<=3) 1/(2i)`), and `integral over S_4(1) of log|u . w| = log||w|| - sum_(i<=3) 1/(2i)`,
  we get `h(Z) = m(g) = log|c| + sum_j log||alpha~_j||`, and `h(Z) >= 0`.
- **`b(F)` (M1, M3).** Mahler measure is multiplicative. A linear form `l` in
  4 variables has `||l||_2 / 2 <= M(l) <= ||l||_2`. So
  `h(Z) - D log 2 <= b(F) <= h(Z)`.

**Distances.** For a point, `Dist(x, alpha) = ||x ^ alpha|| / (||x|| ||alpha||)`.
The import gives `sum_j log Dist(x, alpha_j) <= log Dist(x, Z) + c_1 D`, where
`c_1` is the per-point normalization constant of the eliminant-form definition.
This is the author's own reading of the zero-dimensional case
(hal-00480924, p. 2), and the combination below absorbs any such constant.

**Points at infinity.** `X_0` is defined over `Q` and `Z` is irreducible over
`Q`, so either every `alpha_(j,0)` vanishes or none does.
- If all vanish, then `||x ^ alpha_j|| >= |x_0| ||alpha_j||`. So
  `log Dist(x, Z) >= D (log|x_0| - c_1)`.
- That contradicts (P) once `H > K (c_1 - log|x_0|)`, with
  `|x_0| = 1/||theta~||`.
- So for such `H` every `alpha_(j,0) != 0`, and
  `F = (c prod_j alpha_(j,0)) prod_j u . (1, zeta_j)` with
  `zeta_j = (alpha_(j,1), alpha_(j,2), alpha_(j,3)) / alpha_(j,0) in Qbar^3`.
  Thus `F` is an integral constant times a product of linear forms at affine
  points, as the claim requires.

**Upper bound for `a(F)`.**
- **Restriction.** `F(S_theta v) = c prod_j (v . S_theta^T alpha~_j)`. The map
  `alpha~ -> S_theta^T alpha~` is linear and vanishes exactly on the line
  `C theta~`, since it is the restriction of `u -> u . alpha~` to the hyperplane.
- **Bound per factor.** Hence
  `||S_theta^T alpha~|| <= c_2 ||alpha~ ^ theta~|| / ||theta~|| = c_2 Dist(x, alpha) ||alpha~||`.
- **Sum.** With `M(l) <= ||l||_2`,

  ```text
  a(F)  <=  log|c| + sum_j log Dist(x, alpha_j) + sum_j log||alpha~_j|| + D log c_2
        =   h(Z) + sum_j log Dist(x, alpha_j) + D log c_2.
  ```

- **Degenerate case.** If some factor vanishes identically, `a(F) = -infinity`
  and there is nothing to prove.

**Combination.** Using `b(F) <= h(Z)`, then the distance comparison, then (P):

```text
a(F) + (B-1) b(F) + C deg F
   <=  sum_j log Dist(x, alpha_j) + B h(Z) + (log c_2 + C) D
   <=  -K^(-1) h(Z) Delta + B h(Z)  -  K^(-1) D H + (c_1 + log c_2 + C) D.
```

- **Height terms.** `h(Z) >= 0` and `Delta >= K B`, so the first two terms sum
  to at most 0.
- **Degree terms.** Choose `H > K (c_1 + log c_2 + C + |log|x_0|| + 1)`. Then
  the last two terms sum to at most `-D <= -1`, and the points-at-infinity
  condition holds as well.

So `a(F) + (B-1) b(F) + C deg F < 0`. ∎

**Remarks.**
- Algebraic independence of `z` is not used. Theoreme 1 holds at every point
  of `P_3(C)`.
- The same argument with `n = 2` reproves the `s = 2` input of Part 3 of the
  two-variable artifact, and Part 3 is an elementary special case of it (the
  credit boundary in the import node).
- For `s >= 4` it fails only because Theoreme 1 needs `d >= n - 3`.
- **Unreviewed.** The one reading assumption is how the eliminant-form distance
  on p. 235 is normalized. It can change only `c_1`, which the choice of `H`
  absorbs.
