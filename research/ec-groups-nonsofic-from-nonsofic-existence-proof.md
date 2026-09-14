---
rg: 2
id: ec-groups-nonsofic-from-nonsofic-existence-proof
kind: route
title: Sofic is a model predicate and a nonsofic group exists
target: existentially-closed-groups-are-nonsofic
requires:
  - local-approximation-properties-are-decided-by-ec-groups
  - finitely-presented-nonsofic-group-exists
---

1. Soficity is the local approximation property `P_M` for the model predicate
   "the table has a permutation model with Hamming defect `<= eps` and Hamming
   separation `>= 1 - eps`".  This is the first instance listed in
   `local-approximation-properties-are-marked-closed`.
2. By `finitely-presented-nonsofic-group-exists`, not every group is sofic, so
   (a) of `local-approximation-properties-are-decided-by-ec-groups` fails.
3. By the equivalence (a) ⇔ (b) there, no existentially closed group is sofic.
4. The equivalent formulation is the definition of `P_M` negated at some
   `(F, eps)`.
