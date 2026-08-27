---
rg: 2
id: thompson-pauli-prefix-rounding-proof
kind: route
title: Expect with the coordinate Pauli channel and exactify the residual D8 cell
target: thompson-pauli-prefix-rounding-has-polynomial-cost
requires:
  - thompson-clifford-central-product-tape
  - pauli-generator-average-has-inverse-linear-gap
  - fixed-pauli-pair-hs-rounding
---

On the exact `J=-1` old prefix, finite Stone--von Neumann gives

```text
H=C^(2^n) tensor C^r,
E_n''=M_(2^n) tensor I_r.
```

Apply `(PAG1)` separately to the proposed `P,Q`.  Both are
`O(sqrt(n)delta_n)`-close to the old-prefix commutant.  Conditional
expectation and functional calculus transfer the one-cell relations into
`I tensor M_r`; `fixed-pauli-pair-hs-rounding` then rounds that residual table
with the asserted loss and discarded density.

The sites `x_i` have `O(i)` Thompson addresses.  Every same-site Pauli
relation is a conjugate of the base lamp table, and every distinct-site
commutator is a conjugate of the single off-diagonal orbit relation.  The
finite presentation proof of `thompson-clifford-central-product-tape` gives a
polynomial derivation for each addressed relation.  Fixed-word telescoping
therefore proves `(TPR1)`.  Multiplying by the `sqrt(n)` spectral loss remains
polynomial and hence is accepted by the geometric contraction ledger.
