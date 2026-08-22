---
rg: 2
id: atlas-full-large-no-small-simple-quotient-proof
kind: route
title: Run exact epimorphism classification against small simple targets
target: atlas-full-large-rectangle-has-no-screened-small-simple-quotient
requires:
  - atlas-full-large-rectangle-has-no-a8-a10-quotient
  - atlas-q96-c144-cycle-is-perfect-with-overlap-curvature
---

Use the same finitely presented source and GAP `GQuotients` method as in the
alternating screen.  Exact MSI runs returned the following table:

```text
target       order       epimorphism classes
A8           20160              0
A9          181440              0
A10        1814400              0
PSL3(4)      20160              0
PSU3(3)       6048              0
PSp4(3)      25920              0
M11           7920              0
M12          95040              0
Sp6(2)     1451520              0.                    (SIMP-1)
```

The source is perfect, so every nontrivial finite image is perfect.  A finite
image preserving the four marked vertices has order divisible by 720.  The
targets in `(SIMP-1)` are the first natural simple candidates satisfying that
divisibility and subgroup-scale test, together with the two order-20160
realizations and the independently divisibility-excluded `PSU3(3)`.  Since
`GQuotients` returns all epimorphisms modulo target automorphisms, zero is an
exact exclusion for each named target.
