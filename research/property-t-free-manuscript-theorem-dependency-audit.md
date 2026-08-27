---
rg: 2
id: property-t-free-manuscript-theorem-dependency-audit
kind: claim
title: The current manuscript splits into no-T algebra, two open collapse inputs, and Kazhdan-specific results
artifacts:
  - non_mf_groups_exist.tex
  - metadata/NON_MF_SENTENCE_CENSUS.md
  - research/property-t-free-manuscript-theorem-dependency-audit-proof.md
  - GroupApproximation/Manuscript/OneSidedMFRadical/LiteralMFClosure.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/RankTwelveSimplicity.lean
  - GroupApproximation/Manuscript/OneSidedMFRadical/PrescribedQuotients.lean
---

The current `non_mf_groups_exist.tex` contains three main theorems and fifteen
numbered supporting results.  A theorem-by-theorem audit gives three disjoint
classes.

**Already independent of Property `(T)`.**  These are
`prop:mf-residual-calculus`, `thm:commutant`, `lem:stable-finite`,
`lem:central-corona-corner`, `lem:tau-elementary`, `prop:simple`,
`prop:defect`, `thm:hull`, `lem:saturation`, and `lem:simple-in-defect`,
together with the compressor-containment clause of
`prop:leavitt-compression`.  Their statements and proofs use algebra,
finite-dimensional linear algebra, stable finiteness, or the separately
cited Hull/Osin small-cancellation input, not Kazhdan transport.

**Explicitly Kazhdan-specific and removed from the replacement.**  These are
`thm:compression-criterion`, `lem:kazhdan-projection-order`, `thm:transport`,
`cor:defect-hs`, and `thm:normal-kazhdan`, plus the Property-`(T)` conjuncts
of `thm:headline` and `prop:leavitt-compression`.  They cannot be relabelled
as no-`(T)` results because Property `(T)` occurs in their mathematical
content.

**Two independent open replacement inputs.**

1. `property-t-free-el20-full-mf-radical`, followed by the internal
   `EL_20(R)~=EL_12(R)` rank transfer, supplies the headline with its
   Property-`(T)` conjunct deleted: full MF radical, trivial maps to MF
   groups, non-MF, and the separable stably finite non-MF reduced group
   C-star algebra.
2. `property-t-free-torsion-free-full-mf-radical` supplies the second main
   theorem with its Property-`(T)` conjunct deleted.  It does not follow from
   the Leavitt collapse.  The printed proof uses Property `(T)` independently
   for the torsion-free source, its compression subgroup, and every quotient.

Thus the previous “one analytic input proves every retained endpoint” census
was incorrect for the current manuscript.  Completion requires both open
inputs, then a rewrite which removes the Kazhdan-specific numbered block and
assembles only the retained statements.

The final `Unconditional.lean` must likewise have two unconditional inputs
proved internally and must import no Property-`(T)` or Kazhdan declaration.
No caller-supplied literature premise counts as unconditional.  Historical
attributions which are not used by a numbered theorem may be deleted or kept
explicitly as prose, but they are not part of this dependency claim.
