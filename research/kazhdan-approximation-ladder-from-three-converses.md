---
rg: 2
id: kazhdan-approximation-ladder-from-three-converses
kind: route
title: The three established ring-to-group transfers plus the three open group-to-ring converses give the UN root
target: kazhdan-elementary-approximation-type-mirrors-ring-type
requires:
  - exactly-matricial-rings-have-lef-general-linear-groups
  - lef-el-groups-force-exactly-matricial-simple-ring
  - rank-modelled-simple-rings-give-linear-sofic-projective-el
  - linear-sofic-el-groups-force-rank-model
  - mf-elementary-groups-force-stably-finite-simple-rings
  - stably-finite-simple-rings-have-mf-elementary-groups
  - simple-ring-stably-finite-iff-unit-not-paradoxical
artifacts:
  - research/artifacts/un-blueprint-2026-09-13-part1.md
---

**Derivation.** Throughout, `R` is countable, simple and unital.

- **(L⇐).** If `R` is exactly matricial, `GL_N(R)` is LEF for every `N`
  (`exactly-matricial-rings-have-lef-general-linear-groups`). So is its subgroup `EL_N(R)`.
- **(L⇒).** This is `lef-el-groups-force-exactly-matricial-simple-ring` verbatim.
- **(Σ⇐).** `rank-modelled-simple-rings-give-linear-sofic-projective-el` gives: for a simple `k`-algebra with
  centre `k` and a unital rank model, `S_m = EL_m(R)/(EL_m(R) ∩ k^x 1_m)` is `k`-linear sofic for every
  `m >= 2`.
- **(Σ⇒).** This is `linear-sofic-el-groups-force-rank-model` verbatim.
- **(M⇒).** Suppose `EL_N(R)` is MF for every `N`.
  - Item 2 of `mf-elementary-groups-force-stably-finite-simple-rings`: a nontrivial MF quotient of `EL_N(R)`
    forces `M_m(R)` directly finite for all `m <= N/2`.
  - `EL_N(R)` is nontrivial and MF, so this holds for every `N`. Hence `R` is stably finite.
- **(M⇐).** This is `stably-finite-simple-rings-have-mf-elementary-groups`, in its strong form: every
  `EL_N(R)` is MF.
- **Second equivalence in (M).** `simple-ring-stably-finite-iff-unit-not-paradoxical`, (a)⇔(b).

The route fires only when all three converses are established. Until then the root stays open, and the
established halves are recorded in the root body.
