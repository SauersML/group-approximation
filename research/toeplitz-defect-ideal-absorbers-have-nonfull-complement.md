---
rg: 2
id: toeplitz-defect-ideal-absorbers-have-nonfull-complement
kind: claim
title: Projections of J + T_2 that absorb elements of J mapping to invertibles in the O_3 quotient have non-full complements
invalidates: [toeplitz-defect-ideal-connected-via-absorbing-projections]
---

Notation as in `toeplitz-defect-ideal-unitization-k1-injective`: `A_T = T_2 * T_2`, `e = iota_1(p_3)`,
`J = <e>`, `B_J = J + iota_1(T_2)`. Let `π: A_T -> O_3` be the unital surjection
`iota_1(s_1), iota_1(s_2), iota_2(s_1), iota_2(s_2) -> r_1, r_2, r_3, r_2`.

1. `π(J) = O_3`, and `π(B_J) = O_3`.
2. Let `x ∈ J` with `π(x)` invertible, and `q ∈ B_J` a projection with
   `||qx − x|| < ||π(x)^{-1}||^{-1}`. Then `π(q) = 1`, so `1 − q` is not full in `B_J`.
3. There are `u_0 = 1 + x_0 ∈ U(1+J)` with `π(u_0) = −1`. For these, every projection `q ∈ B_J` with
   `||qx_0 − x_0|| < 2` has non-full complement.

So no family of projections of `B_J` with full complements is an approximate unit for `J`, not even on
the single element `x_0`.
