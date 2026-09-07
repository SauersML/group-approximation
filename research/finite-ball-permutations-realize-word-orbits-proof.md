---
rg: 2
id: finite-ball-permutations-realize-word-orbits-proof
kind: route
title: Extend partial left translations on a finite word ball
target: finite-ball-permutations-realize-word-orbits
requires: []
artifacts:
  - notes/PROPERTY_T_FREE_FINITE_BALL_LIMIT_2026-09-07.md
---

Take a word ball $B_L$ with radius at least every specified word length.
Each partial left translation $g\mapsto s_i g$ whose endpoints are in
$B_L$ extends to a permutation: its domain and range have complements
of equal cardinality. The corresponding permutation matrices and their
inverses agree with left translations along every suffix path of each
specified word starting at $1_G$.

Thus $q(U)\delta_{1_G}=\delta_{q_G}$ for those words. Relators fix
$\delta_{1_G}$ and the nontrivial word sends it to an orthogonal basis
vector. Their difference has norm $\sqrt2$. The artifact supplies the
full statement, inverse-letter check, and scope limits.
