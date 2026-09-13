---
rg: 2
id: lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap
kind: claim
title: A binary linear system is tracially but not R^U-satisfiable exactly when its two CFI-type graphs are qc- but not qa-isomorphic
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
distinct_from:
  lcs-tracial-ru-gap-equiv-nonhyperlinear: that equates a tracial/non-R^U linear system with a finitely presented nonhyperlinear group; this transfers the same gap, in both directions, to the isomorphism game of two finite graphs.
  qc-isomorphic-not-qa-isomorphic-graph-pair-exists: that asks for any qc-but-not-qa graph pair; this proves that the linear-system graph pairs have one exactly when the linear system has the tracial/non-R^U gap.
---

**ESTABLISHED** by `lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap-proof`.

Let `Ax=b` be an `m x n` linear system over `Z_2` with BCS algebra `A(B)`.
For each equation `i`, let `S_i^b` be its local solutions supported on the
variables of that equation.  The graph `G_(A,b)` has vertices `(i,x)` with
`x in S_i^b`.  Two distinct vertices are adjacent when the local solutions
disagree on a shared variable.  These graphs are the FGLSS/CFI-type
construction of Atserias--Mančinska--Roberson--Šámal--Severini--Varvitsiotis,
arXiv:1611.09837, §6, restated as BCEHPSW, arXiv:1812.11474v2, Definition 5.5.

Then the following are equivalent:

1. `A(B)` has a tracial state but no unital *-homomorphism into `R^U`;
2. `G_(A,b) ≅_qc G_(A,0)`, but `G_(A,b)` and `G_(A,0)` are not
   `qa`-isomorphic.

With `lcs-tracial-ru-gap-equiv-nonhyperlinear`, a finitely presented
nonhyperlinear group therefore gives a pair for
`qc-isomorphic-not-qa-isomorphic-graph-pair-exists`.  With
`qc-qa-graph-gap-gives-non-ce-quantum-automorphism-group`, it then gives a
finite graph whose quantum automorphism group is not Connes embeddable.  For
these linear-system pairs the isomorphism gap is exactly as hard as the goal.

**Credit and novelty.**
- **The reduction** is AMRSSV's (arXiv:1611.09837, read at source).
  - Their Theorem 6.5: the BCS game of a linear system has a perfect
    quantum commuting strategy iff `G_F ≅_qc G_(F_0)`.
  - Their Theorem 6.3: the finite-dimensional version.
  - Their Corollaries 6.8 and 6.9: the `qc`/`q` separation and undecidability.
- **The `qa` half** is a direct instance of the hereditary *-equivalence of
  BCEHPSW Theorem 5.6 with Proposition 5.3 at `t = qa`.

So the equivalence itself is a composition of published results.  The part
recorded here as a consequence is the composition with Paddock--Slofstra
Proposition 5.8, which turns a finitely presented nonhyperlinear group into a
qc-but-not-qa graph pair.  A text search of AMRSSV, LMR, BCEHPSW and
Paddock--Slofstra found that composition in none of them.  AMRSSV and BCEHPSW
never mention hyperlinearity, and Paddock--Slofstra never mention isomorphism
games.  This check is bounded to those four papers.
