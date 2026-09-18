---
rg: 2
id: twisted-kazhdan-cone-machine-switch
kind: claim
title: A sofic rank-three twisted Kazhdan cone can be switched by a machine group into a finitely presented family that is sofic exactly on INF
distinct_from:
  rank-three-finite-twisted-kazhdan-cone-is-sofic: that asks whether the core group T_3 is sofic; this asks that, given a sofic core, a machine group can be glued in so that soficity switches exactly on INF.
  kazhdan-double-cones-add-one-sigma1-bit: that proves an untwisted cone carries only one Sigma-zero-one bit; this asks for the twisted replacement, where the centraliser of the edge is not imposed by relations.
  machine-center-vanishes-exactly-on-inf: that is the switching input; this is the gadget that would consume it through a twisted cone.
---

**OPEN.**  Assume `T_3 = (F x Gamma) *_(Gamma_(ev_0)) G` of [[rank-three-finite-twisted-kazhdan-cone-is-sofic]] is
sofic.  Is there a computable family of finite presentations `X_e` with the following two properties?
- If `e ∈ INF`, then `X_e` is sofic.
- If `e ∈ FIN`, then `X_e` contains a double `B *_C B` of a Kun-Thom pair, and so is nonsofic.

The intended shape is a twisted-diagonal cone `(H_e x Gamma) *_(Gamma_(psi_e)) G`, with `H_e` built from `F` and
the machine group of [[machine-center-vanishes-exactly-on-inf]].  On `FIN`, some central element of order two
should centralise `psi_e(Gamma)`, so that (K1) of [[kazhdan-double-cones-add-one-sigma1-bit]] applies.  On `INF`,
`C_(H_e)(psi_e(Gamma))` should be trivial.

**Why it is separate from the core question.**  Soficity of `T_3` is the base case of the positive branch, with
no machine.  A switch also needs soficity to survive the machine, which is an amalgam problem of its own.
