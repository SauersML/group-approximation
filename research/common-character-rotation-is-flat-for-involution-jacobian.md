---
rg: 2
id: common-character-rotation-is-flat-for-involution-jacobian
kind: claim
title: A common code-character rotation is a sharp boundary-flat direction even after adding involution equations
distinct_from:
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that proves a gap transverse to simultaneous conjugation; this shows that physical cut boundary lies in the simultaneous-conjugation kernel and therefore is not controlled by that gap.
  normalized-hs-taylor-remainder-is-not-dimension-free: that uses sparse high-operator-norm perturbations to obstruct pure-HS Newton; this is a two-character smooth tangent with an exact quadratic-versus-linear scaling.
  regularized-anchor-square-function-has-dimension-free-cut: that produces an approximately reducing cut and asks how to carry its leakage; this shows the leakage itself cannot be linearly charged by the selfadjoint-contraction residual phase.
---

ESTABLISHED SHARP FLAT DIRECTION.  Adding the equations `X_i^2=I` to the
balanced Jacobian does not make physical projection-boundary variance
linearly coercive, even at an exact code representation.

Let `chi,psi` be two distinct characters of the exact binary code quotient,
and put

```text
 z_i=1_{chi_i!=psi_i}.
```

Then `z` is a nonzero codeword.  On `C^2` take

```text
 Q_i^0=diag(chi_i,psi_i),       p=diag(1,0),
 Q_i(theta)=U_theta Q_i^0 U_theta^*,
 X_i(theta)=pQ_i(theta)p+(1-p)Q_i(theta)(1-p),          (CCF1)
```

where `U_theta` is the real plane rotation.  The tuple `Q(theta)` is an
exact representation for every `theta`.  With

```text
 c=cos(2theta),       s=sin(2theta),
```

one has

```text
 X_i(theta)=Q_i^0                    if z_i=0,
 X_i(theta)=c Q_i^0                  if z_i=1,           (CCF2)
 ||[p,Q_i(theta)]||_2^2=s^2 z_i,
 ||X_i(theta)^2-I||_2^2=s^4 z_i.                         (CCF3)
```

The contractions `X_i(theta)` commute exactly.  For every dual parity row
`h`, writing `m_h=|h intersect supp(z)|`,

```text
 prod_(i in h)X_i(theta)=c^(m_h)I,
 ||prod_(i in h)X_i(theta)-I||_2^2=(1-c^(m_h))^2.       (CCF4)
```

For bounded row width this is `O_w(s^4)`.  Equality copies can be identical,
so their residual is zero.  Hence, if `rho=|supp(z)|/L`,

```text
 boundary variance=(1/L)sum_i||[p,Q_i(theta)]||_2^2
                  =rho s^2,
 balanced contraction energy <=C_w s^4.                (CCF5)
```

For a positive-distance code, `rho` is bounded below.  Therefore no
dimension- and length-independent linear inequality

```text
 boundary variance <= C * balanced contraction energy  (CCF6)
```

can hold; the square-root exponent is sharp.

Infinitesimally, this is exactly the kernel already present in the balanced
Jacobian.  Differentiating `(CCF1)` at zero gives one common off-diagonal
matrix on `supp(z)`, the simultaneous-conjugation vector in `(QLS3)--(QLS4)`.
For `z_i=1` it anticommutes with `Q_i^0`, so the derivative of
`X_i^2-I` is also zero.  The added involution rows therefore do not remove
the flat direction; they only see it at second order.

There is nevertheless a useful positive conclusion for the proposed
selfadjoint-contraction phase.  If `X=X*` and `||X||_op<=1`, functional
calculus with `S=sign(X)` (choose either sign at zero) gives

```text
 ||X-S||_2^2<=||I-X^2||_2^2.                           (CCF7)
```

Thus involution energy controls the cost of rounding the *pinched
contraction* to a reflection, even though it does not control the boundary
of the pre-pinched reflection.  On `(CCF2)`, sign-rounding returns `Q_i^0`
at cost `(1-c)^2=O(s^4)`, matching the residual scale.  A valid contraction
phase should therefore discard/gauge the common conjugacy boundary and
track contraction-to-sign cost, rather than put boundary variance into a
linearly decreasing Lyapunov.
