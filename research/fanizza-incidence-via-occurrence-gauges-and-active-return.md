---
rg: 2
id: fanizza-incidence-via-occurrence-gauges-and-active-return
kind: route
title: Preserve source cuts with occurrence gauges and defer only the allowed active return
target: gauge-weyl-fanizza-incidence-rounding
requires:
  - gauge-doubling-gives-selector-flip-symmetries
  - two-sided-pauli-gauge-bridge-preserves-spin-scale
  - c18-source-cut-has-sparse-relator-certificate
  - fanizza-c18-residual-factors-through-three-tiny-rank-gates
  - s3-radical-atlas-returns-allowed-active-carrier
  - bounded-overlap-syndrome-energy-accounting
---

Use one private share pair for every variable occurrence while retaining the
original logical word as their product. For each of the three factored C18
gates, condition the Pauli bridge on the complete logical gate tuple before
summing to its literal `p` or `q` child. Since

```text
h p(1-r)<=p,
h q(1-r)<=q,
h p q r<=q,                                             (FOG1)
```

the two exit halves remain inside their named source carriers. The sparse C18
certificate transfers the source cut on the original logical words before any
private gauge correction. Equation `(TPG4)` then renews gauges separately on
every logical atom, so summing forgotten logical coordinates cannot change the
active/exit ledger.

Fixed word-product relations transfer the corrected shares back to the
retained logical words with constant telescoping cost. Bounded-overlap
accounting sums these costs. The only nonlocal input is the allowed active
return: after the first-hit exit is removed, its complement must reduce the
shared Fanizza words and become the next clock carrier. This is precisely the
existing `s3-radical-atlas-returns-allowed-active-carrier` obligation, not a
new selector-renewal defect.

