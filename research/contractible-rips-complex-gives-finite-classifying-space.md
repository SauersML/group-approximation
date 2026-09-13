---
rg: 2
id: contractible-rips-complex-gives-finite-classifying-space
kind: claim
title: A contractible Rips complex of a torsion-free group is the universal cover of a finite classifying space
distinct_from:
  hyperbolic-rips-complex-models-proper-actions: that is the Meintrup–Schick theorem that Rips complexes of hyperbolic groups model proper actions; this is the elementary fact that ANY contractible Rips complex of a torsion-free group gives a finite K(G,1)
---

Let `G` be a torsion-free group (for instance `cd G < ∞`) with a finite
symmetric generating set `S`, and let `r ≥ 1`. If the Rips complex
`R_r(G,S)` is contractible, then `G` acts freely and cocompactly on it, the
quotient `R_r(G,S)/G` is a finite `K(G,1)` of dimension at most `|B_S(r)| − 1`,
and so `G` is of type F.

In particular a yes to Zaremsky Problem 4.6 forces every group of type `F_∞`
with finite cd to be of type F (the remark printed in Problem 4.6), and every
group of type `F_∞` with finite cd that is not of type F has no contractible
Rips complex.

Model tests: `Z` with `S = {±1}` and `r = 1` gives the real line and the circle
as quotient. The hypothesis is needed: `Z/2` with `S = {a}` has contractible
`R_1` (one edge), and its quotient is not a `K(Z/2,1)`.

Proof: `contractible-rips-complex-gives-finite-classifying-space-proof`.
