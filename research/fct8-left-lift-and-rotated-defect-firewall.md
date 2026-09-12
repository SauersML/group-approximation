---
rg: 2
id: fct8-left-lift-and-rotated-defect-firewall
kind: claim
title: The FCT8 left lift preserves mover mass but not fixed range, and rotated defects cost an exponential factor
distinct_from:
  free-compressor-tree-has-constant-first-hit-mover-mass: That constructs the physical leaf exits and computes their half-unit aggregate displacement; this audits the two natural superoperator lifts and the attempted vectorwise Kazhdan summation.
  left-rank-amplification-is-not-a-fixed-sector: That treats one physical projection abstractly; this applies the distinction to the whole free-compressor level and records the dimension-free double-adjoint defect calculus.
  tracial-superoperator-self-copy-has-no-macroscopic-excess: That consumes a positive-density pointwise-fixed range; this proves that the macroscopic left-multiplier projection does not meet that hypothesis.
---

**ESTABLISHED FCT8 AMPLIFIER AUDIT.**  Let `X_w`, `|w|=n`, be the
orthogonal leaf exits of
`free-compressor-tree-has-constant-first-hit-mover-mass`, represented in
`M_d`, and put `K=L^2(M_d)`.  There are two canonical ways to regard an exit
at the adjoint level, and they retain complementary halves of the needed
statement.

### 1. The fixed-vector lift has vanishing density

Let `R_w` be the rank-one orthogonal projection of `K` onto `C X_w`.  Since
`X_w` commutes with the child subgroup `H_w`, the range of `R_w` is
pointwise fixed by `Ad phi(H_w)`.  Orthogonality of the `X_w` makes the
`R_w` orthogonal, but

```text
tr_K(sum_(|w|=n) R_w)=2^n/d^2.                         (FLR1)
```

This is exactly the adjoint-rank loss `(FCT7)`.

### 2. The left-multiplier lift has macroscopic rank but only invariance

Put

```text
E_w=L_(X_w) in End(K),              L_X(Y)=XY.          (FLR2)
```

Then `E_w` are orthogonal projections and

```text
tr_K(E_w)=tau_d(X_w),
tr_K(sum_(|w|=n)E_w)=1/2.                              (FLR3)
```

Moreover, for every physical unitary `U`,

```text
Ad_U L_X Ad_U^(-1)=L_(UXU^*),
||Ad_U L_X Ad_U^(-1)-L_X||_(2,K)=||UXU^*-X||_(2,d).    (FLR4)
```

Thus `(FCT6)` really does lift to half a unit of superoperator mover mass.
However, if `X_w` commutes with `phi(H_w)`, all that follows is

```text
[E_w,Ad(phi(h))]=0,                  h in H_w.          (FLR5)
```

The range `X_w M_d` is invariant, not pointwise fixed.  In fact

```text
(Ad(phi(h))-I)E_w(Y)=X_w(Ad(phi(h))Y-Y),                (FLR6)
```

which is generally nonzero on a macroscopic part of the range.  Therefore
`E_w` is not dominated by the child fixed-vector projection used in
`tracial-superoperator-self-copy-has-no-macroscopic-excess`, and property
`(T)` cannot transport `(FLR3)` to the parent.  Passing to another adjoint
level repeats the same invariant-range/fixed-vector dichotomy.

The defect passage itself is harmless and hence does not repair `(FLR6)`.
For physical unitaries `U,V`, with all norms normalized,

```text
||Ad_U-Ad_V||_(2,K)^2
 =2-2|tau_d(U^*V)|^2
 <=2||U-V||_(2,d)^2.                                  (FLR7)
```

A second adjoint passage costs at most another factor `sqrt(2)`.  Thus the
failure is categorical, not a dimension blow-up in the relator error.

### 3. Orthogonality alone cannot sum the conjugated defects

There is also a sharp finite-dimensional obstruction to the proposed
vectorwise summation before adjoint normalization.  Let `m=2^n`, take `d`
divisible by `2m`, and choose pairwise orthogonal physical projections
`P_1,...,P_m` of trace `1/(2m)`.  Let `R` have the same rank and choose
physical unitaries `U_i` with `U_i R U_i^*=P_i`.  On `K`, set

```text
D=L_R,                    F_i=L_(P_i),
V_i=Ad_(U_i).
```

Then

```text
||D||_(2,K)^2=1/(2m),
sum_i ||V_i D V_i^* F_i||_(2,K)^2
 =sum_i tr_K(F_i)=1/2.                                  (FLR8)
```

Consequently every estimate which controls branchwise conjugates of one
global relator defect using only conjugation invariance and orthogonality,

```text
sum_i ||V_i D V_i^* F_i||_2^2 <= C||D||_2^2,
```

requires `C>=m=2^n`.  This is an exact permutation-matrix example; no
asymptotics or unbounded operators are involved.  A depth-uniform proof of
`(FCT8)` must therefore use an additional relation coupling the prefix
unitaries `phi(v)` to the lamp cylinders beyond the covariance and
orthogonality already recorded.  Neither vectorwise Kazhdan inequalities,
the left-multiplication lift, nor a bare summation of conjugated relator
errors supplies such a coupling.

This does **not** construct a full canonical unitary-HS microstate of the
Kun--Thom wreath and hence does not refute `(FCT8)` with all canonical
relations imposed.  It rigorously closes the two proposed automatic
amplifiers and isolates the remaining possibility: a genuinely joint
prefix-unitary/lamp-algebra recovery theorem.

DERIVATION
fct8-left-lift-and-rotated-defect-proof
