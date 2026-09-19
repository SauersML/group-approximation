---
rg: 2
id: odd-maslov-homogeneous-coefficients-have-a-fixed-size-defect-gap
kind: claim
title: Odd Maslov homogeneous coefficients have a uniform defect gap at every fixed matrix size
distinct_from:
  matrix-homogeneous-ucp-retracts-can-hide-defect: that same-twist Fourier-multiplier construction shows positive defect may be hidden by a split retract; this uses the odd-to-even difference multiplier and proves that, at fixed coefficient size, the hidden defect is bounded uniformly away from zero.
  scalar-covariant-odd-even-ucp-retract-is-impossible: that treats coefficient size one and exact scalar covariance, forcing immediate multiplicativity; this permits arbitrary matrices of fixed size and obtains a compactness gap rather than exact nonexistence.
  maslov-bounded-block-sector-gap: that treats approximate unitary tuples decomposed into bounded common invariant blocks; this treats contractive matrix coefficients of homogeneous ucp maps, which need not be unitary or possess any invariant block a priori.
  odd-maslov-ucp-retract-must-hide-generator-defect: that proves at least one positive defect is nonzero for each retract; this makes the total coefficient defect uniformly positive on every fixed amplification size.
---

Let `Gamma=Sp_4(Z)`, let `alpha` be an odd Maslov multiplier, let `epsilon`
be an even multiplier, and put

```text
delta=alpha epsilon^(-1).                               (OHG1)
```

Thus `delta` is one of the four finite-dimensionally invisible odd Maslov
classes.  Fix a finite symmetric generating set `S` of `Gamma`.

For every `n>=1` there is a constant `kappa_n>0` with the following
property.  If

```text
C:Gamma -> M_n(C),             C_e=I_n,                 (OHG2)
```

is a normalized `delta`-projective positive-definite coefficient function,
then

```text
sum_(s in S) tr_n(2I-C_s^*C_s-C_sC_s^*) >= kappa_n.    (OHG3)
```

Equivalently, suppose a homogeneous ucp map between twisted fibres has

```text
i:C^*(Gamma;alpha) -> M_n(C^*(Gamma;epsilon)),
i(u_g^alpha)=C_g tensor u_g^epsilon.                    (OHG4)
```

Then its coefficient matrices obey `(OHG3)`.  If `i` has a ucp left inverse
`r`, the two positive multiplicative defects of every canonical generator
are killed by `r`, while their total normalized coefficient trace is at
least `kappa_n`.

## Consequence for the surviving retract lane

No sequence of odd-to-even homogeneous split ucp retracts with uniformly
bounded coefficient size can make its hidden generator defect tend to zero.
Any quantitative scalarization attempt that approaches the scalar line by
driving these defects to zero must therefore have

```text
n_k -> infinity.                                        (OHG5)
```

This is the Maslov-specific input absent from
`matrix-homogeneous-ucp-retracts-can-hide-defect`: its same-twist example has
trivial difference multiplier and an honest scalar summand, whereas an odd
difference multiplier has no finite-dimensional projective summand at all.

The compactness proof by itself does not give a lower bound uniform in `n`.
That apparent escape is closed separately by
`odd-maslov-homogeneous-coefficients-have-a-uniform-folner-gap`: direct-
summing the varying coefficient GNS representations converts a vanishing
sequence into a forbidden projective Folner compression.  Thus `(OHG3)` in
fact has one constant valid in every coefficient size.
