---
rg: 2
id: full-mf-radical-uniform-asymptotic-collapse
kind: claim
title: Full MF radical is uniform collapse of operator-norm asymptotic representations
artifacts:
  - research/full-mf-radical-uniform-asymptotic-collapse-proof.md
---

For a countable group `G`, `Rad_MF(G)=G` exactly when every operator-norm
asymptotic representation `(V_n)` satisfies

```text
||V_n(g)-1|| -> 0
```

for every `g in G`.

Consequently `G` is operator-norm matricially stable: every asymptotic
representation is pointwise close to the trivial exact representation in the
same dimensions.

There is also a finite uniform form.  For every finite `F subset G` and every
`epsilon>0`, some finite `E subset G` and `delta>0` force every unitary-valued
map with multiplicative defect below `delta` on `E x E` to satisfy

```text
max_(g in F) ||V(g)-1|| < epsilon.
```

For `H=EL_16(L_(F_2)(1,2))`, every operator-norm asymptotic representation
therefore collapses pointwise to the trivial representation.  If a finite
generating set is chosen, one finite multiplication challenge forces every
generator into any prescribed neighborhood of the identity.
