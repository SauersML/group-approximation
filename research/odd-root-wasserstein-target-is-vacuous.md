---
rg: 2
id: odd-root-wasserstein-target-is-vacuous
kind: claim
title: Wasserstein proximity to odd-root atomic measures imposes no parabolic rigidity
invalidates: [far-sector-from-doubling-plus-coupling]
---

For every probability measure `mu` on the unit circle and every
`epsilon>0`, there is a finitely supported probability measure `nu` whose
support consists entirely of roots of unity of odd order and

```text
W_1(mu,nu)<epsilon.                                      (ORW1)
```

Consequently a modulus asserting only that the empirical parabolic spectral
measure is close in Wasserstein distance to an odd-root atomic measure cannot
repair an approximate representation or close the Iwahori far sector.  The
statement is true without any group relator, doubling invariance, opposite
parabolic, or half-power constraint.

The same issue survives matching the two marginal spectral measures: the
involution `SUS^(-1)=L` already makes their marginals identical, while the
missing rigidity lies in their noncommutative joint eigenvector geometry and
finite multiplicity coupling.  A viable transfer theorem must therefore
control a common operator model (or a fixed finite set of joint moments), not
only scalar spectral measures.
