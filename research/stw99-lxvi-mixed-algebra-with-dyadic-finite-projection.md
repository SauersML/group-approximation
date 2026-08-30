---
rg: 2
id: stw99-lxvi-mixed-algebra-with-dyadic-finite-projection
kind: claim
title: A simple mixed finite-infinite algebra has a coherently dyadically divisible finite projection
---

There exist a simple C\*-algebra `B`, an infinite projection in `B`, a
nonzero finite projection `p in B`, and a sequence `(x_n)` in `V(B)` such that

```text
x_0=[p],                 x_n=2x_(n+1)  for every n.
```

This is an open construction claim.  By
`stw99-lxvi-maximal-finite-corner-criterion`, it is sufficient for Problem
LXVI.

## Attempts

Rordam's mixed finite-infinite simple algebra supplies the first three
objects but does not automatically supply the coherent dyadic chain.  Group
divisibility of `[p]` in `K_0(B)` is only a necessary shadow: it neither
ensures positivity of the roots in `V(B)` nor makes independently chosen
`2^n`th roots coherent.

Tensoring the finite corner `pBp` by CAR cannot install the chain while
preserving finiteness.  Since `pBp` is already non-stably finite, some matrix
amplification has infinite unit, and a sufficiently large CAR matrix stage
carries that isometry into `(pBp) tensor M_(2^infinity)`.

The remaining viable route is internal: alter the projection monoid of a
mixed example so that a finite class has a nested sequence of positive
halves, while preventing any finite partial sum of the resulting CAR tower
from absorbing an ambient infinite projection.
