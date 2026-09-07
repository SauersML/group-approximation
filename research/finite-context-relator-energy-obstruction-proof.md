---
rg: 2
id: finite-context-relator-energy-obstruction-proof
kind: route
title: Enlarge the finite word ball to include every relator context
target: finite-context-relator-energy-misses-nontrivial-words
requires:
  - finite-ball-permutations-realize-word-orbits
artifacts:
  - research/artifacts/finite-context-relator-energy.md
---

Theorems 1 and Corollary 2 in the artifact give the proof. Extend partial
left translations on a ball containing every suffix of every $r_jq$ and
$q$ occurring in $b_j$, as well as $w$. The resulting permutations agree
with the group action on the base vector along each such path, so
$(r_j(U)-I)q(U)\xi=0$. Linearity handles each polynomial context.
The nontrivial word moves the base vector to an orthogonal basis vector.
Evaluating the proposed inequality on this vector gives $2\leq\varepsilon$.
