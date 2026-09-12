---
rg: 2
id: leavitt-range-sum-fold-no-payment-proof
kind: route
title: Tensor the rectangular Weyl cell with two central-character UT4 packets
target: leavitt-range-sum-fold-does-not-pay-reynolds
requires:
  - first-leavitt-weyl-cell-has-exact-rectangular-model
  - leavitt-branch-reynolds-return-has-rectangular-gap
  - carrier-not-decoder
---

The unitriangular calculation gives `(FRN2)`.  Restricting the regular
representation to the nonzero `zeta` spectral space turns its central output
into `zeta I`.  Two tensor-independent copies give one diagonal and one
range nested commutator with the same scalar output; the other range path is
trivial.  This proves `(FRN3)`, including every outer-root commutation.

Tensoring with the rectangular Weyl cell leaves its adjoint Reynolds maps
unchanged after normalized supertrace, because every auxiliary action used
by those packet maps is the identity.  Hence `(FRN1)` and `(FRN3)` coexist,
contradicting `(FRN4)` at zero defect.

For the literal-reuse strengthening, the BCH commutator in nilpotency class
three has degree-three term

```text
[E_12+E_34,[E_23,E_12+E_34]]=2E_14
```

up to the harmless global sign fixed by the commutator convention.  Since
`2` is invertible for `p>=5`, a central character realizes any prescribed
nontrivial phase.  This proves `(FRN5)` and the common-occurrence version of
the countermodel.
