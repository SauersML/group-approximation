---
rg: 2
id: plancherel-sector-meet-sharpness-proof
kind: route
title: Compare repeated and distinct Fourier atoms in one finite abelian packet
target: plancherel-marginals-do-not-control-sector-meet
requires: []
---

The minimal central Fourier idempotents of `C[K]` are pairwise orthogonal,
sum to one, and all have canonical trace `1/N`.  For a repeated atom `e`,

```text
meet_c(1-e)=1-e.                                           (PMS1)
```

For distinct atoms, commutativity and orthogonality give

```text
meet_c(1-e_c)=product_c(1-e_c)=1-sum_c e_c.               (PMS2)
```

Taking canonical traces proves both asserted deficits.  These are exact
finite-dimensional regular representations, so neither pattern can be
excluded by approximate exactification or by one-subgroup Plancherel
marginals.

