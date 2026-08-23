---
rg: 2
id: fournier-facio-asymptotic-representations-trivial
kind: claim
title: Every operator-norm asymptotic representation of the Fournier-Facio group is asymptotically trivial
distinct_from:
  fournier-facio-group-matricially-stable: that claim only asks for closeness to some genuine representations; this stronger claim says the trivial representations themselves always work.
  fournier-facio-group-finite-dimensional-shadow: that claim concerns exact finite-dimensional representations; this one concerns arbitrary operator-norm asymptotic representations of varying dimensions.
  normal-kazhdan-defect-non-mf: that is the general corona killing theorem; this is its concrete consequence after the Fournier-Facio defect is shown to normally generate the whole group.
artifacts:
  - research/artifacts/router-detector-torsion-free-non-mf-2026-08-22.md
  - research/artifacts/fournier-facio-matricial-stability-solution-2026-08-17.md
---

Let `G` be the torsion-free finitely presented Fournier-Facio group fixed in
`fournier-facio-torsion-free-skeleton`.  If

`phi_n : G -> U(k_n)`

is an operator-norm asymptotic homomorphism, then for every `g : G`,

`||phi_n(g) - 1|| -> 0`.

Equivalently, every homomorphism from `G` to the unitary group of a norm
matrix corona is trivial.  In particular the trivial representations are a
pointwise operator-norm correction of every asymptotic representation.

## What the shape of the proof implies

Two readings that the statement alone does not force, recorded when this node
and the retired node *fournier-facio-stability-from-total-corona-triviality*
were merged into one lane (the latter proved the same thing in one step and has
been retired in favour of this factoring; the name is written unbackticked
because it resolves to nothing and is kept only for anyone tracing the merge).

- **The stability it yields is degenerate.**  `G` is matricially stable
  because it admits no nontrivial finite-dimensional approximation at all, not
  because approximate representations of `G` can be repaired.  Reading
  `fournier-facio-group-matricially-stable` as evidence that `G` behaves like
  the uniformly stable higher-rank lattices inverts what these nodes say.
- **It removes an alternative, not just a hole.**
  `torsion-free-non-mf-from-matricial-stability` was kept as the route that
  would still reach the root if `normal-kazhdan-defect-non-mf` turned out to
  have a gap.  Since the stability prerequisite is now proved *from* that
  obstruction, both routes into the root rest on the same analytic theorem and
  a gap in it takes both down together.  The note is carried in that route's
  own body so the graph is not read as two independent confirmations.

## Certification boundary

The analytic input is machine-checked and unconditional
(`normal-kazhdan-defect-non-mf-proof`).  The two group-theoretic inputs are
not formalized: the compression core is read off the published construction,
and `defectNormal = G` is a written Hull argument whose Lean boundary is
`DefectRoutingData`.  So this claim inherits exactly the trust surface of
`torsion-free-non-mf-from-normal-kazhdan-defect` — no more, and no less.
