---
rg: 2
id: existentially-closed-groups-are-nonsofic
kind: claim
title: Every existentially closed group is nonsofic
distinct_from:
  finitely-presented-nonsofic-group-exists: that produces one finitely presented nonsofic group; this shows that a whole canonical class, the existentially closed groups, consists of nonsofic groups.
  local-approximation-properties-are-decided-by-ec-groups: that is the equivalence for an arbitrary model predicate; this is its sofic instance, made unconditional by the established nonsofic existence theorem.
---

**ESTABLISHED** through `ec-groups-nonsofic-from-nonsofic-existence-proof`.

**Statement.**  Every group that is existentially closed in the class of all
groups is nonsofic.  Equivalently, each existentially closed group `H`
contains a finite subset `F` and a tolerance `eps > 0` such that `tab_H(F)`
has no permutation model with Hamming defect at most `eps` and Hamming
separation at least `1 - eps`.

**Remark.**  The corresponding statement with hyperlinear in place of sofic is
equivalent to `non-hyperlinear-group`, by
`local-approximation-properties-are-decided-by-ec-groups`.
