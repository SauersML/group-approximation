---
rg: 2
id: atlas-map-icc-weak-mixing-proof
kind: route
title: Divide by the center and apply minimal almost periodicity to the adjoint representation
target: atlas-map-enemy-has-icc-weak-mixing-factor
requires:
  - atlas-six-relator-nontrivial-quotients-inject-charts
  - atlas-chart-elements-normally-generate-six-relator-group
  - thom-central-corner-criterion
---

Start from the nontrivial hyperlinear MAP quotient `Lambda` and put

```text
Lambda_bar=Lambda/Z(Lambda).
```

The group `Gamma_6` is perfect: it is a quotient of the free product of two
perfect `A8` factors.  Hence `Lambda` is perfect.  If `Lambda_bar` were
trivial, `Lambda` would be both abelian and perfect, hence trivial, a
contradiction.  Thus `Lambda_bar` is nontrivial.

Moreover `Lambda_bar` is centerless.  Indeed, if `x Z(Lambda)` is central in
`Lambda_bar`, then every commutator `[x,g]` lies in `Z(Lambda)`.  Because
these commutators are central, the map

```text
g |-> [x,g]
```

is a homomorphism from `Lambda` to the abelian group `Z(Lambda)` (up to the
irrelevant inverse convention).  Perfectness of `Lambda` makes it trivial.
Thus `x in Z(Lambda)`, proving `Z(Lambda_bar)=1`.

Central-quotient descent in `thom-central-corner-criterion` makes
`Lambda_bar` hyperlinear.  It remains MAP because every finite-dimensional
representation of `Lambda_bar` pulls back to one of `Lambda`.  The composite
map from `Gamma_6` is nontrivial, so quotient rigidity injects both `A8`
charts.  Normal generation by every nonidentity chart element also passes to
this quotient.

To prove ICC, suppose `1 != x in Lambda_bar` has finite conjugacy class.
Conjugation on that class gives a finite permutation representation of
`Lambda_bar`.  Minimal almost periodicity makes this representation trivial,
so every group element fixes `x`; hence `x` is central.  This contradicts
`Z(Lambda_bar)=1`.  Thus every nonidentity conjugacy class is infinite.
Hyperlinearity embeds `L(Lambda_bar)` into `R^omega`, while ICC makes it a
diffuse II1 factor.

Now let `W` be a finite-dimensional invariant subspace of
`L2(M) minus C1` for the conjugation representation.  The restriction to
`W` is a finite-dimensional unitary representation of `Lambda_bar`, hence is
trivial.  Therefore every vector in `W` is conjugation-invariant.  In a
factor the conjugation-invariant vectors in `L2(M)` are `L2(Z(M))=C1`, so
`W=0`.  This is exactly weak mixing of the adjoint representation.

Weak mixing says that for every finite family of vectors and every positive
`epsilon` there is a group element making all corresponding matrix
coefficients smaller than `epsilon`.  Apply this to orthonormal bases of the
two finite-dimensional spaces `V_1,V_2`, and let `epsilon` tend to zero.
Finite dimensionality turns entrywise decay into the operator-norm decay
`(AMW1)`.

Finally, the normal closure of the fixed chart transvection `t` is all of
`Lambda_bar`.  Hence its conjugates generate `Lambda_bar` as a group, and
their left regular unitaries generate `L(Lambda_bar)` as a von Neumann
algebra.  This proves every assertion.
