---
rg: 2
id: orthogonal-kazhdan-power-defect-proof
kind: route
title: Use Pythagoras for the Kazhdan projection, telescope contraction defect, and saturate it by a truncated shift
target: orthogonal-kazhdan-powers-have-quadratic-depth-loss
requires:
  - homogeneous-quotient-near-genuine-microstates-are-deep
  - lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible
---

**Step 1 (one projected intertwiner loses squared mass).**  The finite-group
average onto `I(sigma_1,sigma_2)` is the orthogonal projection `P_I` in
Hilbert--Schmidt space.  Hence `T=P_I(H)` is a contraction and Pythagoras
gives

```text
1-||T||_2^2=||H-T||_2^2=delta^2.                                        (QP1)
```

Let `P_pi^(i)` be the two isotypic projections.  Since `T` intertwines,
`T P_pi^(1)=P_pi^(2)T`.  The corresponding block is a contraction from a
space of normalized dimension `w_1(pi)` to one of dimension `w_2(pi)`, so

```text
||P_pi^(2) T P_pi^(1)||_2^2 <= min(w_1(pi),w_2(pi)).                    (QP2)
```

Sum over `pi`.  Orthogonality of the blocks and `(QP1)` give

```text
1-delta^2=||T||_2^2 <= sum_pi min(w_1(pi),w_2(pi)),                     (QP3)
```

which is `(QK3)`.  This is the quadratic improvement missed by estimating
positive weight differences linearly by `||H-T||_2`.

**Step 2 (powers have an exact square-function ledger).**  For every
contraction `T`,

```text
I-(T^*)^k T^k
 = sum_(i=0)^(k-1) (T^*)^i (I-T^*T) T^i.                               (QP4)
```

Taking normalized trace and using `T^i(T^*)^i<=I` gives

```text
1-||T^k||_2^2
 <= k tau(I-T^*T)
 = k(1-||T||_2^2)
 = k delta^2.                                                           (QP5)
```

If `T^k` intertwines `alpha_k` with `beta_k`, repeat `(QP2)--(QP3)` with
`T^k`.  This proves `(QK4)` directly; no comparison of `T^k` with `H^k`
and no `k delta` operator telescope is used.

**Step 3 (Atkin--Lehner application).**  In
`lambda-exact-p-divisible-ultra-deep-proof`, the Kazhdan average is exactly
the orthogonal projection above, and `T^D` intertwines the restriction to
`C^((D))` with its `Ad(h^D)`-twist.  Multiplication by `rho'(J)` is unitary,
so it does not change its Hilbert--Schmidt norm.  The orbit calculation in
Steps 3--5 of that route identify weight at least
`b_p(1-nu_0)`, `b_p=min(c_p,1/3)`, on
twisted isotypic types absent from the untwisted restriction.  This is a
one-sided overlap deficit, hence is at most `Delta`, and `(QK4)` gives

```text
b_p(1-nu_0) <= D delta_0^2.
```

The Kazhdan estimate `delta_0<=epsilon/kappa_0` proves `(QK5)`.  At depth
one the same replacement improves the balancing error to `delta_0^2`.

**Step 4 (homogeneous-quotient application).**  In
`homogeneous-quotient-deep-tower-proof`, Step 3 again constructs the
orthogonal projection of `H` onto the exact `C_0`-intertwiners, now with
`delta_0<=3epsilon/kappa_0`.  On `C^((k))`, its power `T^k` is the exact
depth-`k` intertwiner.  Thus the overlap deficit used in Step 5 is at most
`k delta_0^2`, rather than `O(k epsilon/kappa_0)`.  Intersecting the fixed
number of signed-permutation conjugates multiplies this by an absolute
constant only.  This proves `(QK6)`.  Comparing it with the unchanged cell
compression upper bound `(DT2)` proves `(QK7)`.

**Step 5 (sharpness and the fence).**  Fix `D` and an orthonormal basis
`e_0,...,e_(D-1)`.  Put

```text
H e_i=e_(i+1 mod D),
T e_i=e_(i+1)  (i<D-1),          T e_(D-1)=0.                            (QP6)
```

Choose a finite cyclic group with distinct characters
`alpha_0,...,alpha_(D-1),psi`.  Let `sigma_1` have diagonal characters
`alpha_0,...,alpha_(D-1)` and let `sigma_2` have diagonal characters
`psi,alpha_0,...,alpha_(D-2)`.  Schur orthogonality says

```text
I(sigma_1,sigma_2)=span{ |e_(i+1)><e_i| : 0<=i<D-1 }.                   (QP7)
```

Thus the orthogonal projection of `H` onto this literal intertwiner space is
`T`.  Directly, `T^k` has rank `D-k`, giving all identities in `(QK8)` and
equality in `(QP5)`.  This example is not asserted to satisfy the full
arithmetic relation packet.  It proves the exact methodological fence:
neither Pythagoras nor a global square function for powers of the single
Kazhdan-projected intertwiner can remove the depth factor.  Any further
improvement must use arithmetic structure absent from an arbitrary
intertwiner space.
