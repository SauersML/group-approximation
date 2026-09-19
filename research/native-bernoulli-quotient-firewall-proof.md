---
rg: 2
id: native-bernoulli-quotient-firewall-proof
kind: route
title: Abelianize the Hecke graph lamps and isolate the first kernel anti-relation
target: no-native-arithmetic-relator-breaks-the-bernoulli-quotient
requires:
  - native-sl3-group-is-hecke-graph-wreath-product
  - native-forty-two-shell-has-a-noncommuting-pair
  - finite-bernoulli-site-decoder-has-schreier-error-floor
  - independent-chart-refinement-forces-eda-leakage
---

For a graph product of copies of `C_2`, adding the commutators of all
nonadjacent vertex generators gives its abelianization
`direct_sum_X C_2`. The actor permutes those commutators, so this quotient is
`A`-equivariant and extends to the semidirect-product map `(NBR2)`. Since it
is a group homomorphism and is the identity on `A`, every actor, section,
root, and conductor identity survives automatically. Pontryagin duality
identifies the lamp group algebra with the product Bernoulli algebra, proving
`(NBR3)`.

All relator energies on the right side of `(NBR4)` therefore vanish in this
finite tracial algebra. A finite polynomial or spectral site decoder is a
finite Bernoulli factor, and its one-hot PVM transport energy is at least
`2 gamma`; this contradicts `(NBR4)`.

By `native-forty-two-shell-has-a-noncommuting-pair`, the two vertices in
`(NBR5)` are nonadjacent. Graph-product normal form gives `kappa!=1`, while
the complete-lamp quotient kills it. The canonical group traces give
`(NBR6)`, and the unitary identity

```text
||rho(kappa)-I||_2^2=2-2 Re tr(rho(kappa))
```

gives `(NBR7)`. Finally, tensoring the raw packet by the identity leaves all
fixed word traces unchanged, while the independent chart refinement of
`independent-chart-refinement-forces-eda-leakage` retains its atomwise exit
floor. This proves that the anti-relation is necessary to exclude the
Bernoulli quotient but is not, as a scalar ledger entry, sufficient to
derive `(EDA11)`.
