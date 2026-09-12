---
rg: 2
id: hs-bounded-kazhdan-transport-proof
kind: route
title: Lift the Kazhdan projection on the Hilbert-Schmidt spaces and estimate in the 2-norm
target: hs-bounded-kazhdan-transport-without-ultraproduct
requires:
  - kazhdan-projection-is-norm-limit-of-finite-averages
  - kazhdan-projection-finite-target-calculus
artifacts:
  - research/artifacts/shorter-proofs-review-2026-09-07.md
---

## Proof

Put `H_n = (M_(d_n)(C), ||.||_2)` and `T_n(g) = Ad(V_n(g))`.  From
`||Ad(A) - Ad(B)|| <= 2||A - B||` the maps `T_n` are asymptotically
multiplicative in the operator norm of `B(H_n)`, so

```text
B = prod_n B(H_n) / sum_n B(H_n)
```

carries a homomorphism `T(g) = [T_n(g)]`.  Let `P in B` be the image of `e_L`
and lift it to orthogonal projections `P_n` on `H_n` by functional calculus.

**The commutant is the range condition.**  Let `(x_n)` satisfy
`M = sup_n ||x_n||_2 < infinity`.

If `||P_n x_n - x_n||_2 -> 0`: from `u_l e_L = e_L` one gets `T(l)P = P`, so
`||T_n(l)P_n - P_n|| -> 0` in `B(H_n)`, and

```text
||T_n(l)x_n - x_n||_2 <= 2||x_n - P_n x_n||_2 + ||T_n(l)P_n - P_n|| M -> 0.
```

Conversely, let `(x_n)` be asymptotically `L`-invariant, fix `epsilon > 0`,
take a probability average `a = sum mu(l) u_l` with `||a - e_L|| < epsilon`
from the prerequisite, and put `A_n = sum mu(l) T_n(l)`.  Then
`||A_n x_n - x_n||_2 -> 0`, being a convex combination of terms tending to
zero, and `limsup_n ||A_n - P_n|| = ||[A_n] - P|| <= ||a - e_L|| < epsilon`.
So

```text
limsup_n ||P_n x_n - x_n||_2 <= epsilon M.
```

Let `epsilon` decrease to zero.  No trivial-character correction appears,
because `mu` is a probability weight.

**Transport.**  `B` is a norm matrix corona with coordinate sizes `d_n^2`
after a choice of matrix units, so it is finite.  Put `U = T(u)`.  Since
`uLu^(-1) <= L`, clause 1 of `kazhdan-projection-finite-target-calculus`
applies in `B` and gives `UPU^* = P`, so `||T_n(u)P_n - P_nT_n(u)|| -> 0`.
Then `||P_n T_n(u)x_n - T_n(u)x_n||_2 -> 0` whenever
`||P_n x_n - x_n||_2 -> 0`, and `||T_n(u)x_n||_2 = ||x_n||_2`, so
`Ad(V(u))` maps `C_2^2(V,L)` into itself; the same argument with `u^(-1)`
in the role of `u`, using `UPU^* = P` again, gives equality.
