---
rg: 2
id: diagonal-copy-nonconjugacy-from-algebraic-relative-commutants
kind: route
title: A unit conjugate to its diagonal copy lies in the relative commutant of rho_w, where every unit over F_2 has finite order
target: leavitt-units-are-not-conjugate-to-diagonal-copies
requires: [leavitt-relative-commutants-are-algebraic-over-every-field]
---

Let `R = L_(F_2)(1,2)` and `phi(y) = s_0 y t_0 + s_1 y t_1`. Suppose `y, w ∈ R^x` and `y = w phi(y) w^(-1)`.

1. `rho_w`, given by `s_i -> w s_i` and `t_i -> t_i w^(-1)`, is a unital endomorphism. The Leavitt relations hold:
   `(t_i w^(-1))(w s_j) = δ_ij` and `Σ_i w s_i t_i w^(-1) = 1`.
2. `y` commutes with `rho_w(R)`. Using `phi(y) s_i = s_i y` and `t_i phi(y) = y t_i`:
   - `y (w s_i) = w phi(y) s_i = (w s_i) y`;
   - `(t_i w^(-1)) y = t_i phi(y) w^(-1) = y (t_i w^(-1))`.
3. By `leavitt-relative-commutants-are-algebraic-over-every-field`, part 3, with `k = F_2`, the unit `y` has finite
   order.

So no unit of infinite order is conjugate to its diagonal copy. ∎

Step 2 is the easy half of the commutant formula in `no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`,
Attempts, step 3, re-derived here so that the route is self-contained.
