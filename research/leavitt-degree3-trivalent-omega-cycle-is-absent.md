---
rg: 2
id: leavitt-degree3-trivalent-omega-cycle-is-absent
kind: claim
title: The shortest ordered degree-three Omega four-cycle is absent from the full packet
artifacts:
  - research/leavitt-degree3-trivalent-omega-cycle-is-absent-proof.md
  - research/artifacts/search-degree3-omega-four-cycle.py
  - research/artifacts/search-degree3-omega-four-cycle.sbatch
distinct_from:
  leavitt-degree3-algebraic-corner-cycle-is-absent: that screens the length-eleven one-one-nine topology after identifying two unary corners; this screens the different one-three-three topology and compares the two whole ordered post-pivot relators.
---

At degree three, the shortest topology with one unary pivot orbit and two
trivalent residual orbits has length seven.  There are exactly fourteen sign
paths.  Across all `14*7!=70,560` placements of the full coefficient packet

```text
(r,e,a,c,b,d,p),
```

solving the unary relation exactly and reducing the quotient of the two
ordered residual relators never gives a conjugate of
`h=[c,d]` or `h^(-1)`.

Thus the minimal trivalent realization of the Omega four-cycle compiler is
not obtained by merely permuting the seven full-packet coefficients.  A
successful realization must use a higher-valence cancellation pattern,
repeat coefficients, or use composite coefficient blocks.
