---
rg: 2
id: cd-two-group-with-infranormal-kazhdan-pair
kind: claim
title: A finitely presented torsion-free group of cohomological dimension two contains an infranormal non-normal Kazhdan pair with a strict compressor
distinct_from:
  hyperbolic-kazhdan-group-has-infranormal-kazhdan-subgroup: that pulls the Leavitt pair back through the Belegradek--Osin hyperbolic cover, whose dimension is not controlled; this pulls it back through the Ollivier--Wise graphical cover, which has dimension two.
  kun-thom-double-of-hyperbolic-pair-has-finite-cd: that gives a nonsofic double of finite but uncontrolled dimension; this supplies a pair inside a dimension-two group, which bounds the double's dimension by three.
  cd-two-groups-have-no-infranormal-kazhdan-pairs: that is the conjectured dimension-two fence; this is its established negation.
---

**ESTABLISHED (unreviewed).** Let `R = L_(F_2)(1,2)`. There are:
- a finitely presented torsion-free group `G` with `cd G <= 2`;
- a surjection `pi : G -> R^x` whose kernel `N` has property (T);
- Kazhdan subgroups `N <= Gamma_hat <= G`, with `Gamma_hat` infranormal and not normal in `G`,
  and an element `u_hat` with `u_hat Gamma_hat u_hat^-1 < Gamma_hat` strictly.

This refutes `cd-two-groups-have-no-infranormal-kazhdan-pairs`: dimension two does not exclude a
strictly compressed Kazhdan subgroup.

**What survives for the Titz--Witzel kernels.**
- The refuted claim was a general fence. The specific question is still open: does some subgroup
  of a Titz--Witzel kernel `K` form such a pair?
- For the Kun--Thom double to certify nonsoficity of `K`, the double itself would have to embed in
  `K`. It cannot: every such double has dimension at least three
  (`compressed-doubles-raise-cohomological-dimension`). The one built here has dimension exactly
  three (`fp-torsion-free-nonsofic-group-of-cd-at-most-three`).

Proof: `cd-two-group-with-infranormal-kazhdan-pair-proof`.
