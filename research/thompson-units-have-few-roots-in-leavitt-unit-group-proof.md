---
rg: 2
id: thompson-units-have-few-roots-in-leavitt-unit-group-proof
kind: route
title: The finite rank bound for Thompson units and the root divisibility lemma
target: thompson-units-have-few-roots-in-leavitt-unit-group
requires:
  - unit-roots-divide-centralizer-rank
  - leavitt-thompson-units-have-finite-centralizer-rank
  - leavitt-north-south-thompson-unit-has-cyclic-centralizer
---

1. `y = w u_g w^(-1)` has infinite order, so it is transcendental over `F_2`
   (`unit-roots-divide-centralizer-rank`, part 3). By `leavitt-thompson-units-have-finite-centralizer-rank`,
   `1 <= rho(y) <= min(N(g), N(g^(-1))) < ∞`.
2. If `y = z^k` with `z in R`, then `z` is a unit (`z^(k-1) y^(-1)` is a right inverse and `y^(-1) z^(k-1)` a
   left inverse), and part 1 of `unit-roots-divide-centralizer-rank` gives `k | rho(y)`. This is part 1.
3. `rho` is a conjugacy invariant: conjugation by `w` carries `C_R(x)` onto `C_R(w x w^(-1))` and intertwines
   the `F_2[x]`- and `F_2[w x w^(-1)]`-module structures. By
   `leavitt-north-south-thompson-unit-has-cyclic-centralizer`, `rho(c) = 1`, so every conjugate of `c` has
   rank 1 and, by step 2, no `k`-th root with `k >= 2`. This is part 2.
4. A nonzero element of `(Q,+)` or `Z[1/p]` has roots of unbounded order inside that subgroup. By step 2 its
   image cannot be a conjugate of an infinite-order Thompson unit. `(Q,+)` lies in `Aff(Q)` and in `GL_n(Q)` for
   `n >= 2` as the unipotent matrices `[[1,q],[0,1]]`, and every nonzero element of that subgroup has roots of
   unbounded order inside it. This is part 3. ∎
