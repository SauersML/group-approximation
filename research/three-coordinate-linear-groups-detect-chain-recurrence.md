---
rg: 2
id: three-coordinate-linear-groups-detect-chain-recurrence
kind: claim
title: General linear rank three detects direct finiteness of zero-dimensional crossed products and gives their exact F2 MF radicals
root: true
distinct_from:
  zero-dimensional-system-mf-radical-is-core-restriction: that uses rank four without period restrictions; this lowers the general linear threshold to three by a different bilateral compression cell, without claiming unrestricted elementary rank three.
  finite-additive-order-one-sided-defects-are-mf-invisible: that needs four elementary coordinates over arbitrary rings; this uses the bilateral shift of a dynamical crossed product to supply the auxiliary levels in three general linear coordinates.
artifacts:
  - research/artifacts/pestov91-three-coordinate-compression-and-involution-localization-2026-09-13.md
  - research/artifacts/check-pestov91-three-coordinate-cell-2026-09-13.py
  - non_mf_groups_exist.tex
---

For a compact metrizable zero-dimensional homeomorphism and any finite
field, GL_n of its algebraic crossed product is MF iff LEF iff the ring
is directly finite iff the whole system is chain recurrent, for n>=3.
Over F2 its MF radical is exactly the locally finite core restriction
kernel, with LEF restriction image as maximal MF quotient.

The proof uses a bilateral diagonal shift corrected by a three-cycle
on negative wandering levels. It creates a finite central compression
defect using three coordinates. The compressor need not be elementary;
the unrestricted EL_3 question is not settled.
