---
rg: 2
id: s4-common-holonomy-morita-blindness-proof
kind: route
title: Factor the common holonomy out of every alternating monomial
target: s4-common-holonomy-charger-is-morita-blind
requires:
  - four-pauli-standard-polynomial-gives-a-fixed-rectangular-gap
  - fixed-packet-correction-retains-multiplicity-gauge
---

# Factor the common holonomy out of every alternating monomial

Because `W` commutes with every packet coefficient, each of the twenty-four
permuted degree-four products has multiplicity factor
`W^(n_1+n_2+n_3+n_4)`.  Factoring it on the right proves `(SCH2)`, and its
unitarity proves `(SCH3)`.  The explicit tensor product `(SCH5)` proves that
authenticating a finite `M_2` packet on the same projection does not
authenticate containment in its scalar matrix factor.  Therefore the only
interpretation on which the standard-polynomial contradiction applies
already contradicts exact completeness when `W=1`; the interpretation that
preserves completeness retains the Morita multiplicity escape.

