---
rg: 2
id: a4-holonomy-gap-from-four-cycle-dirichlet-ceiling
kind: route
title: The one-over-6144 four-cycle ceiling beats the raw S3 energy floor
target: atlas-a4-holonomy-coherence-gap
requires:
  - atlas-a4-four-cycle-dirichlet-ceiling
  - atlas-a8-four-cycle-controls-raw-s3-energy
---

For the four-cycle covariance opcodes,

```text
sum_(t in T) ||[U_n,lambda_(k_n)(t)]||_2^2
 = 2 E_n.
```

Apply `atlas-a8-four-cycle-controls-raw-s3-energy` to the two raw-S3
involutions.  It gives

```text
a_n^2+b_n^2
 <= 24 * 2 E_n
 = 48 E_n.
```

Therefore `(A4-DIR-CEIL)` implies

```text
limsup_n (a_n^2+b_n^2)
 < 48/6144
 = 1/128.
```

This is exactly `atlas-a4-holonomy-coherence-gap`.  Notice that no conclusion
that the relative chart frame approaches an A8 commutant is needed: the finite
word `t21=t01 t30 t23 t30 t01 t30 t23 t30` sends the four-cycle energy directly
to the two covariance coordinates detected by the raw source word.
