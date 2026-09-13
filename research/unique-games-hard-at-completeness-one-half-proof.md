---
rg: 2
id: unique-games-hard-at-completeness-one-half-proof
kind: route
title: Split each 2-to-2 linear constraint into its two unique branches with half weight
target: unique-games-hard-at-completeness-one-half
requires: [two-to-two-games-theorem]
---

Let `U` be an instance of `2-to-2 Game[F_2^l]` from `two-to-two-games-theorem`,
with constraint weights `w_c` summing to `1`. For each constraint
`c : T x_i + T' x_j in {b, b'}`, emit the two linear unique constraints
`T x_i + T' x_j = b` and `T x_i + T' x_j = b'`, each with weight `w_c/2`. Each is
a permutation constraint, `x_j = T'^-1 (T x_i + b)`, because `T, T'` are
invertible. Call the result `U'`. It has polynomial size and the same alphabet.

Fix an assignment `A`.

* If `A` satisfies `c`, then at least one branch holds. Exactly one holds when
  `b != b'`, and both when `b = b'`. So `A` gains at least `w_c/2` in `U'`.
* If `A` violates `c`, then neither branch holds, and `A` gains `0`.
* In every case the gain in `U'` is at most `w_c`.

Hence `val_A(U)/2 <= val_A(U') <= val_A(U)`, and so
`OPT(U)/2 <= OPT(U') <= OPT(U)`. If `OPT(U) >= 1 - eps`, then
`OPT(U') >= (1-eps)/2`. If `OPT(U) <= eps`, then `OPT(U') <= eps`. So the map
`U -> U'` reduces `Gap 2-to-2[F_2^l](1-eps, eps)` to
`Gap-UG[F_2^l]((1-eps)/2, eps)`, and NP-hardness transfers. `square`
