---
rg: 2
id: properly-infinite-unit-group-is-not-mf
kind: claim
title: The unit group of a ring with a full complementary idempotent is not MF
distinct_from:
  full-defect-ring-non-mf-at-rank-two: that is the full-collapse statement for elementary groups, that every homomorphism to an MF group is trivial; this is the weaker non-MF assertion for the whole unit group, where no collapse is claimed.
  binary-leavitt-all-ranks-full-mf-radical: that is the binary Leavitt unit group, where the unit group coincides with every elementary group and full collapse does hold; this is the general ring, where the unit group may be much larger than the elementary subgroup.
  full-complementary-idempotent-elementary-full-mf-radical: that treats the elementary subgroups at rank at least four; this treats the ambient unit group and every GL_n.
artifacts:
  - research/artifacts/rank-two-descent-review-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `R` be a countable unital ring with `s,t` satisfying `ts = 1` and
`R(1-st)R = R`.  Then `R^x` is not MF, and neither is `GL_n(R)` for any
`n >= 1`.

The corner map `jmath` embeds `GL_4(R)`, hence `EL_4(R)`, into `R^x`, and a
subgroup of an MF group is MF.

Only non-MF-ness is claimed here.  Whether every homomorphism from `R^x` to
an MF group is trivial is not asserted; the full-collapse statement is
`full-defect-ring-non-mf-at-rank-two` and concerns the elementary groups.
