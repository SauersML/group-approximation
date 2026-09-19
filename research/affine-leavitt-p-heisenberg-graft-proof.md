---
rg: 2
id: affine-leavitt-p-heisenberg-graft-proof
kind: route
title: Select the native odd Heisenberg character corner
target: affine-leavitt-p-heisenberg-graft-kills-fd-four-cap-corner
requires:
  - affine-leavitt-steinberg-mark-is-fd-invisible
  - edgeful-or3-four-cap-walsh-packet
  - four-cap-two-chart-mixer-has-finite-clifford-evaluator
  - odd-root-cannot-drive-central-d8-actuator
---

Because the coefficient ring has characteristic `p`, the nonzero root
`w=x_12(A)` has order exactly `p`.  Thus `<w,c>` in
`Gamma_A times <c>` is `C_p^2`, matching the standard abelian subgroup of
the order-`p^3` Heisenberg group `(PHG2)`.  The normal-form theorem proves
injectivity of both factors in `(PHG3)`.  It also proves `c!=1`, so every
nontrivial character idempotent `e_chi` is nonzero in `C[Lambda_p]`.

Direct products preserve the two embedded factors and make their group
algebras tensor.  Therefore `(PHG5)` is a nonzero tensor product of
projections.  Canonical traces multiply, giving `(PHG6)`; the same argument
applies to every cap atom below `q`.

For a finite-dimensional representation, apply the exact annihilation
theorem to the `Gamma_A` restriction.  The fixed Heisenberg commutator then
gives `(PHG7)`, and

```text
pi(e_chi)=(1/p) sum_(k=0)^(p-1) conjugate(chi(c))^k I=0
```

because `chi` is nontrivial.  This proves `(PHG8)`.
