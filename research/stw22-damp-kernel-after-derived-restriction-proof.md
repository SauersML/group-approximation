---
rg: 2
id: stw22-damp-kernel-after-derived-restriction-proof
kind: route
title: Extend from the derived set and damp arbitrary isolated-fibre orthogonalizers
target: stw22-derived-set-gap-trace-reduction
requires:
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-derived-set-gap-reduction-audit-2026-08-30.md
---

Put `R=pi_tau(U)''`.  The completion `M(X)` is the algebra of bounded maps
`X -> R` which are continuous in `2`-norm.  Restriction to `Y` is
surjective.  Indeed, the operator-norm ball of radius `C` in `R` is a closed
convex subset of the Hilbert space `L^2(R,tau)`.  The Dugundji extension
theorem extends a `2`-norm-continuous map from the closed subset `Y` to `X`
without leaving that ball.  It can therefore extend every bounded section
of `M(Y)` to one of `M(X)`.

For either base `Z=X,Y`, one has

```text
J_x(Z)={a in K_x(Z): ||a(t)|| -> 0 as t -> x in Z}.      (DSR1)
```

One inclusion follows from multiplication by scalar functions vanishing at
`x`; the other follows by cutting off outside a sufficiently small clopen
neighbourhood of `x`.  Restriction now gives the surjection `(DSR)`.

Let `H=ker(rho_x)`, let `sigma` be a bounded positive trace on `H`, and let
`a` be a positive contraction in `H`.  Lift it to a positive contraction,
still denoted `a`, in `K_x(X)`.  By `(DSR1)`, its restriction to `Y` tends
to zero in operator norm at `x`.

Choose a decreasing clopen local base `(V_n)` at `x` and use its clopen
annuli.  On the `n`-th annulus put

```text
delta_n=sup{||a(t)||:t in Y intersect (V_n\V_(n+1))}.
```

After discarding the complement of `V_1` modulo `J_x(X)`, the locally
constant scalar function with these values and value zero at `x` is
continuous, and `delta_n -> 0`.  Replacing `a` on the `n`-th annulus by

```text
(a-delta_n)_+
```

does not change its class in `I_x(X)` and produces a positive
representative `b` satisfying

```text
b|_Y=0.                                                  (DSR2)
```

Fix `epsilon>0`, put `c=(b-epsilon)_+`, and fix `m`.  Since `b(x)=0` in
`2`-norm, Chebyshev gives, on a sufficiently small clopen neighbourhood of
`x`,

```text
m tau(1_(epsilon,infinity)(b(t))) <= 1.                  (DSR3)
```

The complement of this neighbourhood vanishes in the fibre gap.  Every
point of `X\Y` is isolated.  At each such point choose independently
unitaries `u_1(t),...,u_m(t)` which move the support of `c(t)` onto
pairwise orthogonal projections, and define

```text
v_j(t)=u_j(t)c(t)^(1/2)       (t in X\Y),
v_j(t)=0                      (t in Y).                  (DSR4)
```

Although the unitaries need not vary continuously, every `v_j` belongs to
`M(X)`.  At `y in Y`, `(DSR2)` and `2`-norm continuity of `b` give

```text
||v_j(t)||_2^2=tau(c(t)) <= tau(b(t)) <= ||b(t)||_2 -> 0
```

as `t -> y`.  Thus the square root of the spectral cut damps all
discontinuity of the pointwise choices.

In `H`,

```text
v_j^*v_j=c,
```

while the positive contractions `v_jv_j^*` are pairwise orthogonal.
Therefore

```text
m sigma(c)=sigma(sum_(j=1)^m v_jv_j^*) <= ||sigma||.
```

Arbitrariness of `m` gives `sigma(c)=0`, and then `epsilon -> 0` gives
`sigma(a)=0`.  Hence `H` is bounded-trace-free.

Every bounded positive trace on `I_x(X)` vanishes on `H` and factors through
`I_x(Y)`; conversely, every trace on `I_x(Y)` pulls back along `(DSR)`.
This proves `(DSR-TF)`.  Iterating through finitely many derived sets ends
at an isolated point, where `J_x=K_x`, and proves the finite-height
consequence.
