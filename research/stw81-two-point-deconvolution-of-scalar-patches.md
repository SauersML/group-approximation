---
rg: 2
id: stw81-two-point-deconvolution-of-scalar-patches
kind: route
title: Invert two scalar mixtures and invoke projectionless overlap degeneracy
target: stw81-shared-unit-two-chart-patching-forces-af
requires:
  - stw81-projectionless-rotating-overlap-degeneracy
---

Fix a contraction `a in E union {1_D}` and abbreviate

```text
X=T^0(a),                    Y=T^1(a).
```

The two approximation assumptions say

```text
norm(lambda X+(1-lambda)Y-a)<epsilon,
norm(mu X+(1-mu)Y-a)<epsilon.                         (SUP1)
```

Subtracting gives

```text
abs(lambda-mu) norm(X-Y)<2epsilon,
norm(X-Y)<2epsilon/kappa.                             (SUP2)
```

Using either convex combination again,

```text
norm(X-a)
 <=norm(lambda X+(1-lambda)Y-a)+(1-lambda)norm(X-Y)
 <epsilon+2epsilon/kappa,

norm(Y-a)
 <=norm(lambda X+(1-lambda)Y-a)+lambda norm(X-Y)
 <epsilon+2epsilon/kappa.                             (SUP3)
```

This proves (SUT5) simultaneously on the finite set and at the unit.  No
positivity is needed for this deconvolution step.

Now put

```text
a_i=phi_i^0 psi_i^0(1_D),
b_i=phi_i^1 psi_i^1(1_D).
```

These are positive contractions, (SUT4) gives `a_i b_i=0`, and (SUP3) at
the unit gives

```text
norm(1-a_0-a_1)<delta,
norm(1-b_0-b_1)<delta.                                (SUP4)
```

Scale both pairs by `(1+delta)^(-1)`.  They become subunital pairs with
unit defect at most

```text
eta=2delta/(1+delta).
```

For sufficiently small `epsilon`, one has `eta<1/8`.  Apply
`stw81-projectionless-rotating-overlap-degeneracy`.  One of `a_0,a_1` has
norm at most

```text
(1+delta)(1-sqrt(1-8eta))/2,                          (SUP5)
```

which tends to zero with `epsilon`.  Since the positive map

```text
phi_i^0 psi_i^0:D->D
```

has norm equal to the norm of its value `a_i` at the unit, discarding this
colour changes the approximation in (SUP3) by at most (SUP5).  The
remaining factorization has one c.p.c. order-zero return map.  Letting
`epsilon` tend to zero gives nuclear dimension zero, hence `D` is AF.

For (SUT6), choose points `s,t in J` for which

```text
abs(g(s)-g(t))>=kappa.
```

Evaluation of the global approximation at `s,t` gives (SUP1).  If both
localized maps from one local frame were assigned the same global colour,
that frame is already one-coloured and (SUP3) gives the conclusion.
Otherwise each frame uses both global colours.  Since a genuine transition
has a point where `g(1-g)>0`, order zero of either global colour gives

```text
phi_i^0(F_i^0) phi_i^1(F_i^1)=0
```

after matching its two labels.  Thus (SUT4) holds and the abstract theorem
applies.

It remains to justify (SUT8).  Put

```text
A=T^0(1_D),                    B=T^1(1_D).
```

Each is the sum of two returned positive contractions, so
`norm(A),norm(B)<=2`.  Formula (SUT7) on the coordinate function gives

```text
Phi(id tensor 1)(1)-Phi(id tensor 1)(0)
 =(g(1)-g(0))(x_0A-x_1B).                            (SUP6)
```

Because `0<=x_0A,x_1B<=2`, their difference has norm at most two.  If the
two endpoint values approximate respectively zero and one within
`epsilon`, their difference has norm at least `1-2epsilon`.  Taking norms
in (SUP6) yields

```text
1-2epsilon<=2 abs(g(1)-g(0))<=2 osc(g),
```

which is (SUT8).
