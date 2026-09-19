---
rg: 2
id: punctured-congruence-inexactness-proof
kind: route
title: Delete one point from regular congruence actions and patch the broken arrows
target: punctured-congruence-actions-are-inexact-on-every-fixed-level
requires: []
---

Choose the primes and punctured left translations `(PCA2)--(PCA3)`.  A
product of two patched translations differs from the corresponding exact
left translation at at most two input arrows, while the patched product
translation differs at one, proving `(PCA4)`.  The same one-arrow comparison
with the fixed-point-free regular action proves `(PCA5)`.

For each fixed congruence level, choose the two commuting root elements in
`(PCA6)`.  The selected primes avoid that level, so both reductions remain
distinct nontrivial commuting elements.  The direct evaluation `(PCA7)`
shows that their punctured permutations fail to commute.  This holds for
all first `j` levels simultaneously.  Restoring the deleted identity point
recovers the exact regular congruence action with relative dimension error
`1/(|Q_j|-1)`, proving the flexible-correction assertion.
