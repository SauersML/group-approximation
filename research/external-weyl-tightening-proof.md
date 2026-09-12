---
rg: 2
id: external-weyl-tightening-proof
kind: route
title: Factor the external frame operator out of the defect Gram sum
target: external-weyl-tightening-is-only-column-weighting
requires:
  - tight-defect-cubic-is-weighted-fusion-frame
---

Summing `(EWT2)` and applying `(EWT1)` gives `(EWT3)` directly.  Since every
`c_i` is positive, the join of the enlarged family is

```text
(join_i r_i) tensor I.
```

The fusion-frame characterization
`tight-defect-cubic-is-weighted-fusion-frame` now says that tightness is
equivalent to

```text
sum_i c_i r_i=mu(join_i r_i)
```

for one scalar `mu`.  That is exactly the original weighted internal
problem.
