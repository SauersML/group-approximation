---
rg: 2
id: zero-cycle-approximation-via-philippon-conjecture
kind: route
title: Philippon's degree-height budget turns sum of log distances into a ratio against Mahler measure that grows like D
target: algebraically-independent-points-approximable-by-zero-cycles
requires:
  - philippon-zero-cycle-approximation-conjecture
---

Apply [[philippon-zero-cycle-approximation-conjecture]] in `n = s` to
`x = (1 : z_1 : ... : z_s)`, with `D > 2 B c_n` and `H` large. The cycle `Z` is
defined over `Q`. Its primitive Chow form is
`F = c prod_j (u . alpha~_j)`, taking representatives `alpha~_j` with integral
normalization.

* **Upper bound for `a`.** By (M1), and (M3) from above,
  `a(F) <= log|c| + sum_j log ||alpha~_j (x) theta~||`, where `(x)` is the exterior
  product. This equals

  ```text
  log|c| + sum_j log Dist(x, alpha_j) + sum_j log ||alpha~_j|| + D log ||theta~||.
  ```

* **Lower bound for `b`.** By (M3) from below,
  `b(F) >= log|c| + sum_j log ||alpha~_j|| - deg(Z) log sqrt(s+1)`.
* **Height comparison.** `h(Z)` and `b(F)` differ by `O(deg Z)`, the standard
  comparison between Mahler measure and projective height of zero-cycles.
* **Combine.** With `c'` depending on `s` and `z`,

  ```text
  a + (B-1) b + C deg Z  <=  sum_j log Dist + B b + c' deg Z
                         <=  -c_n^(-1) (h(Z) D + deg(Z) H) + B h(Z) + c'' deg Z.
  ```

  This is negative once `D > B c_n` and `H > c_n c''`, since `h(Z) >= 0`.
* **Points at infinity and components in `Y`.** They are at positive distance
  from `x`. Corollary 6 of Part 2 absorbs them into the constant, once the
  hyperplane at infinity is added to `Y`.

This route and the `s`-variable transcription in
`full-atiyah-base-change-via-cycle-approximation` together make the full Atiyah
base change under the determinant conjecture a consequence of Philippon's
conjecture.
