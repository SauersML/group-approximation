---
rg: 2
id: mixed-steinberg-triangles-transfer-actor-additivity
kind: claim
title: Mixed Steinberg triangles transfer uniform actor-root additivity to the active module
distinct_from:
  steinberg-actor-preserves-right-ratio-orbitals: that gives an exact partial graph-product escape when only transported commutator rows are imposed; this proves that the escape cannot satisfy the full mixed triangles together with an additive actor root.
  steinberg-root-shear-plancherel-covariance: that decodes one fixed finite Fourier window and its shear permutation; this is a window-free algebraic and normalized-HS estimate conditional on a uniform remote actor-root table.
  affine-leavitt-steinberg-hs-coefficient-decoder: that seeks coefficient multiplication in one relative Leavitt cell; this transfers additive root multiplication only and isolates the remaining self-similar actor-root gate.
---

Let `B=AR` be the affine active corner.  Fix distinct indices `i,j,6` and
use the root pattern

```text
X(a)=x_ij(a),       C=x_j6(A),       Y(a)=x_i6(a).       (MST1)
```

In an exact Steinberg system,

```text
X(a+b)=X(a)X(b),
Y(a)=[X(a),C],
[X(b),Y(a)]=1.                                       (MST2)
```

These three rows force

```text
Y(a+b)=Y(a)Y(b)                                      (MST3)
```

for every `a,b in B`.  Thus the right-ratio partial graph product from
`steinberg-actor-preserves-right-ratio-orbitals` cannot be extended to a
model of all the rows `(MST2)` while retaining a missing same-root product.

The implication is uniformly normalized-Hilbert--Schmidt quantitative.
Suppose unitary-valued maps `X,Y` and a unitary `C` satisfy, uniformly in
`a,b`,

```text
||Y(a)-[X(a),C]||_2 <= epsilon,
||X(a+b)-X(b)X(a)||_2 <= epsilon,
||[X(b),Y(a)]-I||_2 <= epsilon.                       (MST4)
```

Then

```text
||Y(a+b)-Y(a)Y(b)||_2 <= 6 epsilon.                   (MST5)
```

For the five active coordinates choose one spare actor root for each and
write `Y_i(a)=x_i6(a)`.  If `(MST4)` holds for each coordinate and the
cross-coordinate root commutators have defect at most `eta`, then the fixed
ordered section

```text
phi(a_1,...,a_5)=Y_1(a_1)...Y_5(a_5)                  (MST6)
```

satisfies the all-pairs bound

```text
||phi(a+b)-phi(a)phi(b)||_2
 <= 30 epsilon+10 eta.                                (MST7)
```

The constants do not depend on coefficient addresses or matrix dimension.

This is an exact finite algebraic closure theorem, but not yet the desired
finite-presentation decoder.  Its premise contains the uniform additive
table of the remote actor root `a |-> x_ij(a)`.  A fixed presentation gives
that table pointwise, with word/area constants depending on `a,b`; it does
not give the supremum in `(MST4)`.  The affine active-module exposure problem
has therefore become self-similar in a precise way: mixed triangles transfer
uniform additivity from actor roots to last-column roots at constant loss,
but they do not manufacture uniform actor-root additivity.

