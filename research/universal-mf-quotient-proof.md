---
rg: 2
id: universal-mf-quotient-proof
kind: route
title: Diagonalize detecting corona models of the radical quotient
target: universal-mf-quotient
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md
  - GroupApproximation/Sofic/ActualCoronaMFRadical.lean
  - GroupApproximation/Sofic/ManuscriptExactWrappers.lean
---

## Direct proof

Put `R = Rad_MF(G)` and `Q = G/R`.  Every nonidentity element of the
countable group `Q` has a lift outside `R`, so some corona representation
detects that lift; every corona representation kills `R` and descends to
`Q`.  Enumerate the nonidentity elements of `Q`, choose one detector for
each, and diagonalize finite initial blocks of their matrix models.  This
produces one faithful positive natural-dimension corona representation of
`Q`.  Composing it with `G -> Q` gives one representation of `G` whose
kernel is exactly `R`.

If `f : G -> M` and `M` is MF, composing `f` with a faithful corona
representation of `M` shows that `R` lies in `ker(f)`, so `f` factors
through `Q`.  A faithful representation of `G` forces `R` to be trivial,
while triviality of `R` identifies `G` with the MF quotient `Q`.  These four
conclusions are packaged by `manuscriptUniversalMFQuotient`.
