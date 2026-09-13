---
rg: 2
id: linear-seam-languages-make-normal-labels-effective
kind: route
title: Enumerate linear-complexity quadratic Sturmian windows, evaluate right-multiplied normal forms and test each restriction
target: sturmian-seam-normal-and-mf-consequence-is-polynomial-time
requires:
  - finite-elementary-abelian-subgroup-controls-all-seam-normals
  - directed-seam-mf-closure-is-cycle-pruning
  - binary-subshift-language-has-quadratic-group-witnesses
  - subshift-elementary-group-word-problem-degree
artifacts:
  - research/artifacts/pestov91-finite-normal-control-2026-09-13.md
  - research/artifacts/solve-pestov91-sturmian-consequence-2026-09-13.py
  - research/artifacts/check-pestov91-finite-normal-control-2026-09-13.py
  - research/artifacts/pestov91-control-algebra-receipt-2026-09-13.json
---

Section 4 counts `h+1` words per tagged endpoint and exactly `h`
marker placements per edge. Quadratic rotation cuts and the fixed
mechanical point enumerate them with polynomial bit complexity.
Binary phase enumeration preserves linear word complexity. On each
length-`2L+1` window, right multiplication maintains nine arrays of
Laurent coefficients and costs `O(L^2)` for the whole word. The
linear number of windows gives the stated field-operation bound.
Apply the test on each endpoint and edge closure to obtain the
minimal normal label of a word. Coordinate unions and cycle closure
then decide both consequence problems.

The exact solver implements these steps. Its bounded MSI audit includes
264 independent finite-matrix comparisons, exact language checks through
length 16, and restricted marking identities. These checks support the
implementation; they do not replace the written proof.
