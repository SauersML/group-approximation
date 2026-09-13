---
rg: 2
id: circle-rotation-zd-derived-full-groups-are-not-fp
kind: claim
title: Derived and alternating full groups of free circle rotation codings are not finitely presented
distinct_from:
  periodic-approximable-subshifts-host-no-fp-simple-group: that kills every finitely generated subgroup for subshifts with periodic approximations; this kills the derived and alternating full groups of circle rotation codings over Z^d through finite type, without checking the stabilizer clause of periodic approximations
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part3.md
---

**ESTABLISHED (unreviewed).** Let `X` be the closure of a coding of a free `Z^d`-action
on the circle by rotations, by finitely many half-open arcs
(`circle-rotation-zd-codings-are-not-of-finite-type`).
- `D([[Z^d ~ X]])` and `A([[Z^d ~ X]])` are not finitely presented.
- No finitely presented subgroup of `[[Z^d ~ X]]` contains the rule 3-cycles of any radius.

**Why it matters for Zaremsky Problem 1.10.**
- For minimal faithful `Z^d`-subshifts, `D([[Z^d ~ X]])` is finitely generated,
  infinite and simple (`minimal-z2-subshift-derived-full-groups-are-fg-simple`).
- For `d = 2` these systems include the free rank-2 interval exchange realizations. ChJN
  (arXiv:1602.04255, line 88, quoted in
  `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md`) record that JMMdlS proved
  those groups amenable.
- So this family of finitely generated infinite simple amenable groups is never
  finitely presented. The root `fp-infinite-simple-amenable-group` listed these systems
  as unchecked.

**Scope.** Only free actions, with 1 and the angles rationally independent, and one fixed
partition.
