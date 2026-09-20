---
rg: 2
id: rips-doubles-bcc-via-tree-action
kind: route
title: "Apply hyperbolic coefficient assembly at both vertices of the Rips double"
target: rips-doubles-satisfy-bc-with-coefficients
requires: ["ollivier-wise-kazhdan-rips-construction", "hyperbolic-bcc-finite-wreath-products", "bcc-passes-from-tree-vertex-stabilizers"]
artifacts:
  - research/artifacts/torsion-free-nonhyperlinear-rips-double-2026-09-20.md
---


The finite Ollivier–Wise construction gives word-hyperbolic G.
The hyperbolic coefficient theorem follows from the second prerequisite
by taking its finite outside group to be trivial. Its classical source
is Vincent Lafforgue, [arXiv:1201.4653](https://arxiv.org/abs/1201.4653),
J. Noncommutative Geometry 6 (2012), 1–197; this theorem was rechecked
2026-09-20 and needs no fresh nonhyperlinearity input.

P acts without inversions on its Bass–Serre tree; vertex stabilizers
are conjugates of G. Apply the tree prerequisite. This proves the
claim for every Gamma, without requiring H to be amenable or quasiconvex.
