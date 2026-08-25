---
rg: 2
id: bounded-exponent-lef-group-defeats-burnside-mf-program
kind: claim
title: An infinite finitely generated bounded-exponent LEF group would defeat both Burnside MF targets
distinct_from:
  lef-implies-operator-mf: that is the general positive theorem for every countable LEF group; this records its exact consequence for the proposed bounded-exponent non-MF mechanism.
  corona-restricted-burnside-equals-power-law-moduli: that compares the corona statement with restricted-Burnside relator moduli and uses the finite restricted Burnside group; this firewall needs neither those relators nor restricted Burnside finiteness.
  operator-norm-restricted-burnside: that asserts that no such infinite corona subgroup exists; this gives the explicit conditional countermodel supplied by LEF windows.
---

Let `G` be an infinite, finitely generated LEF group of exponent dividing
some finite `N`.  Then `G` is operator MF and an injective homomorphism from
`G` into a norm matrix corona has infinite image of exponent dividing `N`.
Consequently both of the following proposed statements are false whenever
such a `G` exists:

```text
operator-norm-restricted-burnside,
infinite-fg-bounded-exponent-groups-are-non-mf.
```

This is a conditional firewall, not an existence assertion.  In particular,
it neither asserts that an infinite free Burnside group is LEF nor imports
anything about the status of that question.

