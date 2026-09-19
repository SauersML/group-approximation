---
rg: 2
id: leavitt-hyperlinear-nonsofic-via-fold-mf-trace
kind: route
title: Put the surviving presentation-double fold word in the sofic radical of its MF-trace quotient
target: hyperlinear-nonsofic-group
requires:
  - leavitt-presentation-double-has-all-fold-mf-moments
---

**REFUTED RADICAL-COLLISION ROUTE.** For `t<1`, the MF trace `tau_t` makes
its GNS group image `H_t` hyperlinear and keeps the fold word nontrivial.
The proposed additional step was to put that image of the fold word in
`Rad_sof(H_t)`; this would make `H_t` nonsofic and prove the target.

This route is refuted for the Hall/tensor family: its coordinates are signed
permutation matrices, so
`leavitt-hall-tensor-mf-trace-quotients-are-sofic` proves every resulting
`H_t` is sofic and has trivial sofic radical.
