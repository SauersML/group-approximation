---
rg: 2
id: non-linear-sofic-via-sigma-converse-at-leavitt
kind: route
title: Rung Σ⇒ of the unification ladder at the binary Leavitt algebra gives a group that is not F_2-linear sofic
target: non-linear-sofic-group
requires:
  - linear-sofic-el-groups-force-rank-model
  - leavitt-algebras-l-k-1-n-are-simple
  - leavitt-center-is-coefficient-field
  - leavitt-algebra-has-no-unital-rank-model
artifacts:
  - research/artifacts/un-sigma-converse-2026-09-13.md
---

## Why sufficient

- `R = L_(F_2)(1,2)` is a simple unital `F_2`-algebra (`leavitt-algebras-l-k-1-n-are-simple`), with
  centre `F_2` (`leavitt-center-is-coefficient-field`). So it meets the hypotheses of
  `linear-sofic-el-groups-force-rank-model` with `k = F_2`.
- `R` has no unital homomorphism into any rank ultraproduct over any field
  (`leavitt-algebra-has-no-unital-rank-model`), in particular over `F_2`.
- By the contrapositive of (Σ⇒), some `S_N = EL_N(R)/(EL_N(R) ∩ F_2^x 1_N)` with `N >= 2` is not
  `F_2`-linear sofic. Since `F_2^x = {1}`, `S_N = EL_N(R)`.
- `EL_N(R)` is countable. So it is a countable group that is not `F_2`-linear sofic, which is
  `non-linear-sofic-group` with `F = F_2`.

## Firewall, the reason this route matters

(Σ⇒) is at least as hard as the famous root `non-linear-sofic-group`. A proof of (Σ⇒) needs ring rigidity
of rank models of EL_N over a ring with no rank model. That is exactly what
`el3-rank-models-factor-through-ring-rank-models` asks for over characteristic-p fields, and
`non-linear-sofic-via-el3-ring-rank-rigidity` routes it to the same root. Conversely, a refutation of
(Σ⇒) would need a simple rankless k-algebra all of whose projective elementary groups are k-linear sofic.
At `L_(F_2)(1,2)` that is `binary-leavitt-unit-group-is-f2-linear-sofic`, still open.
