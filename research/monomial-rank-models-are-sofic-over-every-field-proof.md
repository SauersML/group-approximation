---
rg: 2
id: monomial-rank-models-are-sofic-over-every-field-proof
kind: route
title: Rank is column-Hamming on monomials; push labels to the circle by a generic character, round to roots of unity, take the skew product
target: monomial-rank-models-are-sofic-over-every-field
requires: []
artifacts:
  - research/artifacts/ex-q34-monomial-phases-2026-09-12.md
---

Complete proof in the artifact, sections 1 and 2.

*Lemma.*  For monomials `A, B` over `K`, the columns where they differ
define a multigraph of maximal degree two, whose components are loops,
paths and cycles.  Their ranks are `1`, `L` and `>= L - 1`.  So
`|Q|/2 <= rank(A - B) <= |Q|`.

*Theorem.*  Replace the generators by nearby monomials and extend to words.
Subadditivity of rank keeps relators within `C eps` and test words at
`>= delta - C eps`.  By the lemma, relator holonomies equal `1` exactly on
columns of density `>= 1 - 2C eps`, and test words move columns of density
`>= delta - C eps`.  The labels generate a finitely generated
`Λ ≅ Z^a × Z/q <= K^x`, because torsion in a field's multiplicative group is
cyclic.  A generic character `psi : Λ -> U(1)` with faithful torsion part
keeps the finitely many exact equalities and inequalities of holonomies.  The
exact relator constraints define a closed subgroup of the torus
`U(1)^(S_0 × [N])` containing `psi ∘ d`.  Torsion points are dense in it, and
the inequalities are open, so some torsion point of order `m` satisfies all
constraints.  The skew product on `[N] × Z/m` is an exact action of the free
group.  Relators fix every point over a good column, and a point fixed by a
test word lies over a column fixed by the monomial model.  Uniform weak
separation gives soficity by Elek--Szabó amplification.
