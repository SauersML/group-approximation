---
rg: 2
id: subshift-rank-four-mf-dichotomy-proof
kind: route
title: Join finite ring models to the printed rank-four torsion-defect theorem
target: subshift-elementary-mf-iff-word-edges-lie-on-cycles
requires:
  - subshift-ring-lef-iff-word-edges-lie-on-cycles
  - finite-additive-order-one-sided-defects-are-mf-invisible
  - elementary-groups-over-fg-rings-have-property-t
  - unit-idempotent-elementary-group-has-three-torsion-generators
artifacts:
  - research/artifacts/pestov91-subshift-lef-mf-dichotomy-2026-09-13.md
  - research/torsion-defect-one-auxiliary-coordinate-proof.md
---

Sections 3--5 give the proof. Ring-LEF gives finite models for every
matrix-group table by including inverse entries; LEF then implies
operator MF. If the graph condition fails, the ring claim constructs
`ts=1` with nonzero defect `1-st` of additive order equal to the field
characteristic. Apply the printed one-auxiliary-coordinate route of the
finite-order defect theorem to kill its elementary root in every MF
image at rank at least four.

Finite ring generation and Ershov--Jaikin-Zapirain give finite generation
and property (T). In binary characteristic two, the earlier triple
generates the upper-left rank-three group; the constant swap of
coordinates 3 and 4 supplies the remaining root positions. A bad graph
is a finite-language certificate, so the complement of the MF locus is
open. The monotone binary subshift has the transient edge `01`, and
its defect is exactly the indicated transition cylinder.
