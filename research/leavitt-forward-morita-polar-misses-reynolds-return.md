---
rg: 2
id: leavitt-forward-morita-polar-misses-reynolds-return
kind: claim
title: The natural Leavitt Morita coefficient polar points in the wrong Reynolds direction
distinct_from:
  mixed-steinberg-loops-admit-morita-rectangular-model: that proves all typed multiplication triangles survive rectangular object spaces; this computes the natural left-right coefficient superoperator, its exact algebraic inverse, and why its polar cannot supply source-saturated Reynolds compression.
  iterated-leavitt-self-similarity-is-dual-prefix-matrix-chart: that identifies the exact ring isomorphism with a matrix chart; this audits the Hilbert-space Gram of its first-step coefficient realization under arbitrary object gauges.
  affine-leavitt-source-saturated-reynolds-checksum: that asks for a contraction from the larger source commutant range into the smaller target commutant range; this refutes the obvious attempt to obtain it by polar-correcting the native Morita coefficient map.
---

**ESTABLISHED FIREWALL.**  Let `E` be a finite-dimensional complex Hilbert
space, put `F=E direct_sum E`, and let `s_i:E->F`, `t_i:F->E` be the
coordinate inclusions and projections.  For any invertible `G in GL(F)` set

```text
x_i=G s_i,                 y_i=t_i G^(-1).              (MCP1)
```

Then exactly

```text
y_i x_j=delta_(i,j)I_E,
sum_i x_i y_i=I_F.                                      (MCP2)
```

Hence every Leavitt inverse/range-sum identity and every typed Steinberg
composition triangle is independent of `G`.

The most direct mixed-coefficient superoperator is

```text
C_G:End(E)->End(F),
C_G(A)=sum_i x_i A y_i=G(A direct_sum A)G^(-1).         (MCP3)
```

It is an algebraic unital embedding for every `G`.  On its range the
algebraic inverse is obtained by either diagonal coefficient:

```text
t_i G^(-1) C_G(A) G s_i=A.                             (MCP4)
```

More locally, `C_i(A)=x_iAy_i` has algebraic inverse
`D_i(B)=y_iBx_i` on the typed corner `x_i y_i End(F)x_i y_i`.

These inverse formulas do not control Hilbert adjoints.  With the
Hilbert--Schmidt inner products,

```text
C_i^*=L_(x_i^*) R_(y_i^*),
C_i^*C_i=L_(x_i^*x_i) R_(y_i y_i^*),                  (MCP5)
```

whereas the algebraic inverse is `D_i=L_(y_i)R_(x_i)`.
The identities `(MCP2)` place no bound on the difference.  When
`dim(E)>=2`, take `G` block diagonal and let its restriction to the first
coordinate block have singular values `a` and `a^(-1)`.  Then `C_0` contains
the similarity `A |-> HAH^(-1)` with `H=diag(a,a^(-1),...)`, whose Hilbert
condition number is unbounded as `a->infinity`, while every relation in
`(MCP2)` and every composition triangle remains exact.  Thus a polar
perturbation estimate for `C_G` is not a formal consequence of the typed
coefficient multiplication identities.  A unitary microstate decoder could
in principle add genuinely analytic information which selects a near-unitary
object gauge; the next paragraph grants that strongest correction and shows
that the resulting polar still points in the wrong direction.

The perturbative ledger isolates the missing analytic row exactly.  Suppose
`x,y` are contractions supported between two decoded orthogonal projection
corners, put

```text
epsilon_inv=||yx-e||_2,       epsilon_*=||y-x^*||_2.    (MCP5a)
```

Then

```text
||x^*x-e||_2<=epsilon_inv+epsilon_*,
||yy^*-e||_2<=epsilon_inv+epsilon_*.                    (MCP5b)
```

Indeed subtract `yx` from `x^*x` in the first line and from `yy^*` in the
second.  Using
`||L_aR_b||_(HS,super)=||a||_2||b||_2` and `(MCP5)` gives, with the same
normalization on the source corner,

```text
||C_i^*C_i-I_(eEnd(E)e)||_(HS,super)
 <=2(epsilon_inv+epsilon_*).                           (MCP5c)
```

Thus the inverse-product word defect `epsilon_inv` is not the obstacle; the
unpaid term is precisely the complex-adjoint identification
`epsilon_*`.  Decoding the Whitehead block as a unitary on one common
physical carrier would control that term, but
`literal-prefix-three-root-swap-retains-typed-carriers` proves that the
current typed packet does not authenticate that common carrier.

Even imposing the optimal gauge does not produce the needed Reynolds map.
If `G` is unitary, `y_i=x_i^*` and, with normalized Hilbert--Schmidt norms,

```text
||C_G(A)||_(2,F)^2
 =Tr(2 copies of A^*A)/(2 dim E)
 =||A||_(2,E)^2.                                      (MCP6)
```

So `C_G` is already an exact isometry.  But its direction is

```text
source label algebra -> doubled target label algebra.  (MCP7)
```

This is precisely the rectangular label amplification.  The required
finite-matrix obstruction goes in the opposite direction: it must inject the
larger source **commutant** Reynolds range, of normalized rank `p^(-2)`, into
the smaller target commutant range, of normalized rank `p^(-4)`.  Polarizing
`C_G` cannot reverse label and multiplicity, and `(MCP6)` holds in the exact
rectangular countermodel.

Consequently the native coefficient formula supplies neither missing input:

1. typed multiplication controls its algebraic inverse but not its Hilbert
   adjoint under arbitrary coefficient-category object gauges; and
2. after a unitary polar correction it authenticates the already-allowed
   label-amplifying direction, not the forbidden source-saturated commutant
   compression.

A successful `X_U` in
`affine-leavitt-source-saturated-reynolds-checksum` must therefore be built
from a genuinely cross-typed **return Gram** that reverses the Morita arrow
on multiplicity coordinates.  It cannot be the polar part of the native
forward coefficient chart or any expression determined only by `(MCP2)`.
