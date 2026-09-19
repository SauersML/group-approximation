---
rg: 2
id: finite-prototype-column-collision-proof
kind: route
title: Apply centralizer-area properness type by type and count cyclic-coset fibres
target: finite-prototype-column-codes-force-coset-collisions
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Fix a vertex `v` of type `i`.  Conjugating its edge fillings by `b_v^(-1)`
does not change area.  Substituting `beta_i` for the normalized word
`b_v^(-1)h_vb_v` in the two occurrences in a commutator adds at most `2B`
cells.  Thus all normalized neighbour rows lie in `C_Gamma(beta_i)` and have
commutator area at most `A+2B` against `beta_i`.

Properness of finite-mark centralizer area gives a finite number `D_i` of
`<beta_i>`-cosets with that bound.  Put `D=max_i D_i`.  If every coset fibre
contains at most `K` neighbours, the out-degree of every vertex is at most
`KD`.  The inherited orientation on every induced subgraph has at most `KD`
times as many edges as vertices, so its average undirected degree is at most
`2KD`.  Greedy deletion and reinsertion gives a `(2KD+1)`-colouring.

For the root-separated specialization, two normalized elementary-root rows
in one cyclic coset differ by an element of the intersection of that root
subgroup with `<beta_i>`.  If the intersection is trivial, distinct
coefficients give distinct cosets, so `K=1` and the same bound applies.
