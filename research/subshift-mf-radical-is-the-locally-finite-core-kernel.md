---
rg: 2
id: subshift-mf-radical-is-the-locally-finite-core-kernel
kind: claim
title: Every finite-alphabet subshift elementary group over F2 in rank at least four has exact locally finite MF radical and LEF cycle-core quotient
root: true
distinct_from:
  subshift-elementary-mf-iff-word-edges-lie-on-cycles: that detects whether the MF radical is nonzero; this identifies its entire kernel and its maximal MF quotient for every subshift.
  directed-seam-mf-radical-is-exactly-the-acyclic-edge-kernel: that computes radicals for finitely many directed seams; this removes that hypothesis completely at rank at least four.
artifacts:
  - research/artifacts/pestov91-cycle-core-exact-mf-reflection-2026-09-13.md
---

For every nonempty finite-alphabet subshift `X`, its cycle core `Y`,
and `n>=4`, the MF radical of `EL_n(LC(X,F_2) semidirect Z)` is exactly
the kernel of restriction to `Y`. This kernel is locally finite and
the restriction quotient is `EL_n(LC(Y,F_2) semidirect Z)`, which is LEF.
The same radical formula holds for `GL_n`, with maximal MF quotient
the image of restriction. No general linear surjectivity is asserted.
