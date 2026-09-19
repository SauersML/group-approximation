---
rg: 2
id: finitely-presented-sofic-non-mf-proof
kind: route
title: Combine literal soficity with the literal MF failure
target: finitely-presented-sofic-non-mf
requires: [literal-group-sofic, literal-group-fails-mf-conventions, sofic-implies-hyperlinear]
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - non_mf_groups_exist.tex
---

## Why sufficient

`E` is finitely presented by `def:E` (forty-one relators; thirty-two on six
generators after Tietze elimination).  `literal-group-sofic` gives soficity,
`sofic-implies-hyperlinear` upgrades it to hyperlinearity, and
`literal-group-fails-mf-conventions` gives failure of every formalized MF
convention.  Corollary 5.2 of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`.

Radical form: `Rad_sof(E) = 1` because `E` is sofic
(`sofic-radical-soficization`), while `w != 1` lies in `Rad_MF(E)` by
`literal-central-mark-corona-invisible` — the two radicals separated on a
single finitely presented group.
