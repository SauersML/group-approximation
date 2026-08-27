---
rg: 2
id: atlas-high-order-mixing-return-proof
kind: route
title: Move all syllables off both finite charts inside the weakly mixing Leavitt factor
target: atlas-relators-keep-high-order-return-under-mixing
requires:
  - atlas-six-relator-leavitt-tracial-countermodel
  - atlas-map-enemy-has-icc-weak-mixing-factor
  - binary-leavitt-unit-group-is-minimally-almost-periodic
  - binary-leavitt-elementary-group-is-simple
  - leavitt-unit-group-has-no-finite-normal-subgroup
  - atlas-charts-overlap-trivially
---

The binary Leavitt group `Q` is minimally almost periodic.  It is ICC by
`leavitt-unit-group-has-no-finite-normal-subgroup`, so `M=L(Q)` is a factor.
Exactly as in the adjoint step of `atlas-map-icc-weak-mixing-proof`, a
finite-dimensional invariant subspace of `L2(M) minus C1` would give a
finite-dimensional unitary representation of `Q`; MAP makes that action
trivial, while factoriality leaves no centered invariant vectors.  Hence the
adjoint representation is weakly mixing.

Let `F` be the finite set of nonidentity group elements which occur as
syllables in the six reduced words, and put

```text
V_i=L2(A_i) minus C1.
```

Weak mixing gives a sequence `g_n in Q` for which

```text
max_(x in F, i in {1,2})
 ||P_(V_i) lambda(g_n x g_n^-1)||_2 -> 0.              (AHR4)
```

For a group unitary and a subgroup algebra, canonical Fourier expectation
is discrete:

```text
E_(L(H))(lambda(y)) = lambda(y)  if y in H,
                       0          otherwise.           (AHR5)
```

Every norm in `(AHR4)` is therefore either zero or one.  Choose one large
`n`; then all are zero simultaneously.  This is `(AHR1)`.

The same argument in the canonical group factor of the conditional quotient
`Lambda_bar` from `atlas-map-enemy-has-icc-weak-mixing-factor` gives the same
zero-return element there: that quotient is ICC, its adjoint representation
is weakly mixing, and both finite charts inject.  Hence the high-order return
pattern is compatible with the exact structure of the hypothetical CE enemy,
not only with `Q`.

For a relator `r=x_1...x_m`, multiplication before expectation gives

```text
product_k lambda(g x_k g^-1)
 =lambda(g (product_k x_k) g^-1)
 =lambda(g r g^-1)=1,
```

which proves `(AHR2)`.  This also pinpoints the invalid inference in a
one-letter correlation expansion: `E_(A_i)` is linear and bimodular over
`A_i`, but it is not multiplicative on the moved chart tuple.

Simplicity makes every nonidentity transvection a normal generator.  The
regular chart traces and positive `h_5` value are exactly the established
Leavitt tracial countermodel.  Hence every listed property coexists in this
single factor, completing the no-go.
