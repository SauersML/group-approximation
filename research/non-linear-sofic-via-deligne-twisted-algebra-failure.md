---
rg: 2
id: non-linear-sofic-via-deligne-twisted-algebra-failure
kind: route
title: A one-sided inverse over a Deligne-twisted group algebra makes the triple cover non-linear-sofic
target: non-linear-sofic-group
requires:
  - deligne-twisted-group-algebra-is-not-stably-finite
  - linear-sofic-group-algebra-is-stably-finite
artifacts:
  - research/artifacts/deligne-twisted-group-algebras-2026-09-12.md
---

1. The padded pair of `deligne-cover-nonsurjunctive-from-twisted-algebra-failure` makes `F[E_3]` not stably
   finite for a finite field `F` of characteristic `p != 3`.
2. By `linear-sofic-group-algebra-is-stably-finite`, `E_3` is not `F`-linear sofic.
3. Since `F_p`-models are `F`-models, `E_3` is not `F_p`-linear sofic either.

*Verification by `w4-vf-linear-b` (2026-09-12), Section 27 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. This is the contrapositive of `linear-sofic-group-algebra-is-stably-finite`, and the target asks only for some field.*
