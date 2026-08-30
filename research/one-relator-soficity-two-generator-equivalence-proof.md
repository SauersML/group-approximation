---
rg: 2
id: one-relator-soficity-two-generator-equivalence-proof
kind: route
title: Separate the torsion case and compress the torsion-free case
target: one-relator-soficity-is-torsion-free-two-generator-case
requires: [one-relator-two-generator-torsion-spectrum-embedding]
---

Statements 1=>2=>3 are immediate. Assume statement 3 and let `G` be a
one-relator group.

If `G` is torsion-free and finitely generated, then
[[one-relator-two-generator-torsion-spectrum-embedding]] embeds it in a
torsion-free two-generator one-relator group `H`. The hypothesis makes
`H` sofic, and soficity passes to subgroups.

If `G` has torsion, Wise, *The Structure of Groups with a Quasiconvex
Hierarchy*, Annals of Mathematics Studies 209 (2021), Theorem 19.1 and
Corollary 19.2, proves that one-relator groups with torsion are virtually
compact special. They are therefore residually finite and hence sofic.
Minasyan--Zalesskii, *One-relator groups with torsion are conjugacy
separable*, J. Algebra 382 (2013), Theorem 1.1, gives hereditary conjugacy
separability and is a direct residual-finiteness backstop.

If the convention allows an infinite generating alphabet, only finitely many
generators occur in the relator. Then `G=G_0*F`, where `G_0` is the
finitely generated one-relator group on the support and `F` is free.
The preceding paragraphs make `G_0` sofic, and free products of sofic
groups are sofic. Thus statement 3 implies statement 1. QED
