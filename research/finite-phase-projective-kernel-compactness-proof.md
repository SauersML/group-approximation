---
rg: 2
id: finite-phase-projective-kernel-compactness-proof
kind: route
title: Compactify the character-face exclusion inside its normal graph subgroup
target: projective-kernel-face-gap-compactifies-phase-safely
requires: []
---

Intersect the weak-star closed fixed faces

```text
{phi:phi(conjugate(chi(k))k)=1}
```

with the compact set `closure(S_fd(G))`.  Their total intersection is empty
by `(PKC1)`, so compactness supplies a finite subfamily with empty
intersection.  Conjugation invariance gives

```text
(1,g)(chi(k)^(-1),k)(1,g)^(-1)
 =(chi(gkg^(-1))^(-1),gkg^(-1)),
```

so the full graph `(PKC3)` is normal.  The normal closure of the finite
subfamily stays in that graph, which meets the scalar factor trivially.
