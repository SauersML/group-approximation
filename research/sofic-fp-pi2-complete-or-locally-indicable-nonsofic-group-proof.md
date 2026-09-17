---
rg: 2
id: sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group-proof
kind: route
title: The sofic Rice criterion splits on whether the locally indicable rope is sofic
target: sofic-fp-pi2-complete-or-locally-indicable-nonsofic-group
requires: [compiler-rope-is-locally-indicable, finite-presentation-rice-criterion-via-the-fixed-positive-rope, finitely-presented-nonsofic-group-exists, sofic-recognition-finite-presentations-arithmetical-position]
---

**Case 1: every `R_e` (`e in INF`) is sofic.**  Take `P` = sofic.
- `P` is isomorphism-invariant and passes to subgroups.
- (C1) is the case hypothesis.
- (C2) holds by [[finitely-presented-nonsofic-group-exists]].

By [[finite-presentation-rice-criterion-via-the-fixed-positive-rope]], `SOFIC_fp` is `Pi^0_2`-hard.  By
[[sofic-recognition-finite-presentations-arithmetical-position]], `SOFIC_fp in Pi^0_2`.  So `SOFIC_fp` is
`Pi^0_2`-complete, which is branch (a).

**Case 2: some `R_e` with `e in INF` is not sofic.**  `R_e ≅ R'_e` is finitely presented (item 9 of the MF
assembly artifact cited in [[compiler-rope-is-locally-indicable]]).  By [[compiler-rope-is-locally-indicable]] it
is locally indicable, hence left-orderable and unique-product.  This is branch (b).  ∎

**Calibration of the criterion on a property that the rope has.**
- Replace "sofic" by "torsion-free".  Case 1 applies because the rope is torsion-free
  ([[mf-compiler-positive-branch-is-torsion-free]]).  It yields the `Pi^0_2`-completeness of torsion-freeness on
  finite presentations, which agrees with Lempp's theorem as cited in
  [[arithmetical-complexity-table-of-group-properties]].
- Replace "sofic" by "residually finite".  Case 2 applies, and correctly yields only a finitely presented locally
  indicable group that is not residually finite (`R_e` is not residually finite by construction).  That is
  consistent with known examples.

So the split produces no false witness on either side.
