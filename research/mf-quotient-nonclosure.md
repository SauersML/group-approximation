---
rg: 2
id: mf-quotient-nonclosure
kind: claim
title: MF groups are not closed under quotients
distinct_from:
  literal-mark-quotient-mf: This proved counterexample uses the quotient F_8 onto E; the open claim asks whether the different quotient E/<w> is MF.
  mf-extension-nonclosure: This claim exhibits failure under quotients; the other exhibits an extension with MF kernel and quotient but non-MF total group.
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralMFQuotientControls.lean
---

The residually finite rank-eight free group `F_8` is MF and its canonical
presentation map surjects onto the literal eight-generator finitely
presented group `E`, but `E` is not MF.  Hence the class of MF groups is not
closed under quotients.
