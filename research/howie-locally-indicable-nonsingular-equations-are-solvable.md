---
rg: 2
id: howie-locally-indicable-nonsingular-equations-are-solvable
kind: claim
title: Nonsingular one-variable equations over locally indicable groups inject their coefficients
distinct_from:
  klyachko-kl-holds-for-torsion-free: that covers every torsion-free coefficient group but only exponent sum ±1; this covers every nonzero exponent sum and every t-shape, but only locally indicable coefficient groups.
  torsion-free-amenable-t-shape-adjunctions-are-aspherical: that covers torsion-free coefficient groups at amenable t-shapes; this has no shape hypothesis and needs local indicability instead.
  kervaire-laudenbach-holds-for-hyperlinear: that derives the conjecture from an approximation property; this derives it from local indicability, with no approximation input.
artifacts:
  - research/artifacts/kl-nonamenable-shapes-2026-09-13.md
---

Let `G` be locally indicable and `w in G * <t>` with `deg_t(w) != 0`. Then the
coefficient map `G -> (G * <t>)/<<w>>` is injective.

This is the one-variable, one-equation case of Howie, *On pairs of 2-complexes
and systems of equations over groups*, J. Reine Angew. Math. 324 (1981),
165--174. Klyachko--Thom record that Howie proved the Gerstenhaber--Rothaus
theorem for locally indicable groups. That theorem asks for
`H_2(X; Z) = 0`, where `X` is the presentation complex of `<x | x^m>`, with
`m = deg_t(w)`. The cellular boundary of the single 2-cell is multiplication
by `m`, so `H_2(X; Z) = 0` exactly when `m != 0`. "Solvable over `G`" means
that some overgroup of `G` contains a root, which is equivalent to injectivity
of the coefficient map above.

There is no hypothesis on the `t`-shape of `w`, and none on reduction:
`w` may be conjugate to `t^m`.

Imported second hand; see the citation route for what was read.
