---
rg: 2
id: slofstra-wagon-wheel-embedding-citation
kind: route
title: Import Slofstra's constructive wagon-wheel solution-group embedding theorem
target: slofstra-solution-group-embedding-preserves-marked-involutions
requires: []
---

William Slofstra, *Tsirelson's problem and an embedding theorem for groups
arising from non-local games*, J. Amer. Math. Soc. 33 (2020), 1--56,
Theorem 3.1 (Theorem `T:embedding` in the supplied source), states exactly:
for a finitely presented group `G`, a specified central involution `J'`, and
a finite sequence of specified involutions `w_i`, there is a solution group
and an embedding preserving `J'` as the solution-group sign `J` and sending
each `w_i` to an edge generator.

The proof is constructive.  It first embeds the group over `Z_2` into a
finite collegial presentation by involutions, then builds the finite
wagon-wheel hypergraph, and proves injectivity by the constellation theorem
and van Kampen pictures.  The source explicitly notes that a Turing machine
computes the hypergraph, labelling, and embedding words from the input
presentation.  These are precisely the assertions in the claim.
