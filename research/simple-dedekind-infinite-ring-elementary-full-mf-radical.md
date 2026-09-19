---
rg: 2
id: simple-dedekind-infinite-ring-elementary-full-mf-radical
kind: claim
title: Every countable simple unital ring that is not directly finite has elementary groups with full MF radical from rank four
distinct_from:
  full-complementary-idempotent-elementary-full-mf-radical: that is the criterion on one complementary idempotent; this is its consequence for the whole class of simple rings with a one-sided unit, where fullness is automatic.
  binary-leavitt-algebra-not-directly-finite: that is the failure of direct finiteness in one algebra; this is what such a failure implies for the elementary groups of any countable simple ring.
artifacts:
  - non_mf_groups_exist.tex
---

Let `R` be a countable simple unital ring that is not directly finite, i.e.
containing `s, t` with `ts = 1 ≠ st`.  Then for every `n ≥ 4` every
homomorphism from `EL_n(R)` to an MF group is trivial.

Simplicity of `R` is used only to make the nonzero idempotent `1 - st` full;
simplicity of the group `EL_n(R)` plays no role.  Printed as the first half
of `cor:simple-infinite-ring`.
