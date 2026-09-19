---
rg: 2
id: atlas-full-large-rectangle-has-no-a8-a10-quotient-proof
kind: route
title: Enumerate exact alternating epimorphisms of the full six-generator presentation
target: atlas-full-large-rectangle-has-no-a8-a10-quotient
requires:
  - atlas-full-large-rectangle-is-balanced-s720-two-cycle
---

The verifier presents the universal group on `r,z,c,u,t,s`.  Besides the
finite-vertex relators of the Q96--C144 cycle, it imposes the two remaining
large-rectangle cubes

```text
((u r)t)^3=1,       (r s)^3=1.                         (ALT-1)
```

For each target `A_n`, GAP computes all epimorphisms modulo target
automorphisms using `GQuotients`.  The exact outputs are

```text
target       order       epimorphism classes
A8           20160              0
A9          181440              0
A10        1814400              0.                    (ALT-2)
```

Since there are no epimorphisms at all, there is nothing to pass to the
secondary filter checking marked subgroup orders

```text
|L|=60,       |F'|=36,       |J|=24,       |C|=144.
```

The calculations ran on MSI with exact permutation groups; no random search
or floating-point test is involved.
