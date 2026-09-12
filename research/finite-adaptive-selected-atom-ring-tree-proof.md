---
rg: 2
id: finite-adaptive-selected-atom-ring-tree-proof
kind: route
title: Adjoin one conditional Murray-von Neumann arrow at every bounded tree edge
target: finite-adaptive-selected-atom-ring-tree
requires: []
---

For each of the finitely many edges, freely adjoin a partial-isometry pair
with source `a_(sigma,i)` and a new range projection orthogonal to the
current carrier, then define the child carrier to be their orthogonal sum.
This gives `(FAR1)--(FAR2)` by presentation.  Cyclicity of finite matrix
trace gives

```text
tr(d)=tr(ss*)=tr(s*s)=tr(a),
```

which proves `(FAR3)`.  In the perfect BCS representation every source `a`
vanishes, so sending all new arrows and ranges to zero satisfies every new
relation and leaves all carriers equal to the Pauli seed.  Finiteness follows
from the fixed depth and branching number.
