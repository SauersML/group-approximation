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
