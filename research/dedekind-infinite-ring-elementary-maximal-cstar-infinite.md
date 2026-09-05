---
rg: 2
id: dedekind-infinite-ring-elementary-maximal-cstar-infinite
kind: claim
title: The maximal group C-star algebra of EL_n over any countable ring that is not directly finite contains a proper isometry
distinct_from:
  maximal-group-cstar-infinite-under-strict-compression: that is the group-level theorem, for any group with a strictly compressed Kazhdan subgroup; this is the ring-level instance, showing that failure of direct finiteness of the coefficient ring alone, with no fullness, already supplies such a compression in rank four.
  leavitt-unit-group-algebra-not-directly-finite: that asks whether the modular group algebra of the Leavitt unit group is directly finite; this is about the maximal C-star algebra of elementary groups over an arbitrary ring with a one-sided unit, and is established.
  full-complementary-idempotent-elementary-full-mf-radical: that needs the complementary idempotent full and concludes non-MF; this needs it only nonzero and concludes the weaker, maximal-algebra statement, without asserting non-MF.
artifacts:
  - non_mf_groups_exist.tex
---

Let `R` be a countable unital ring that is not directly finite.  Then for
every `n ≥ 4`, `C*_max(EL_n(R))` contains a proper isometry; so it is not
stably finite, has no faithful tracial state, and is neither residually
finite-dimensional nor MF.

Whether `EL_n(R)` is itself non-MF under this hypothesis alone is not
asserted.  Printed as `cor:one-sided-ring-maximal`.
