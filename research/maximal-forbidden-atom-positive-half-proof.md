---
rg: 2
id: maximal-forbidden-atom-positive-half-proof
kind: route
title: Pigeonhole the robust forbidden mass and apply the one-bit selector
target: maximal-forbidden-atom-has-a-named-positive-half
requires:
  - non-ce-bcs-has-robust-approximate-energy-gap
  - central-sign-assignment-atom-is-index-two-reynolds-surplus
  - one-bit-clifford-selector-halves-a-chosen-bcs-atom
---

The compressed robust BCS inequality gives

```text
sum_(i=1)^M tau(E_i)>=beta tau(Q)-C sqrt(E).
```

The largest summand is at least `1/M` of the sum.  Equation `(OCS4)` then
retains one half of that summand, proving `(MFA2)`.  Since the menu is fixed,
choosing the maximizing index after seeing the matrix tuple introduces no
dimension-dependent constant and requires no new group generator.

Before the optional half cut,
`central-sign-assignment-atom-is-index-two-reynolds-surplus` identifies that
same maximal `E_i` with the compression of a literal Reynolds difference.
This proves `(MFA1a)` and shows that `(MFA1)` already carries operator-valued
type data with no factor-two loss.
