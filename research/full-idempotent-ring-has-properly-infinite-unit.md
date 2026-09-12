---
rg: 2
id: full-idempotent-ring-has-properly-infinite-unit
kind: claim
title: A full complementary idempotent is the same as a properly infinite unit
distinct_from:
  full-complementary-idempotent-elementary-full-mf-radical: that is the analytic theorem about elementary groups over such a ring; this is the purely ring-theoretic reformulation of its hypothesis and mentions no group and no MF target.
  simple-dedekind-infinite-ring-elementary-full-mf-radical: that specializes the analytic theorem to simple rings, where fullness is automatic; this identifies what the fullness hypothesis says in any ring.
  binary-leavitt-algebra-not-directly-finite: that is the failure of direct finiteness in one algebra, a strictly weaker condition; this is the equivalence of the fullness upgrade with proper infiniteness.
artifacts:
  - research/artifacts/rank-two-descent-review-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `R` be a nonzero countable unital ring.  The following are equivalent.

1. There are `s,t in R` with `ts = 1` and `R(1-st)R = R`.
2. There are `v_0,v_1,w_0,w_1 in R` with

```text
w_i v_j = delta_(ij) 1        (i,j in {0,1}).       (PI)
```

Under (PI) the elements `p_i = v_i w_i` are orthogonal idempotents each
equivalent to `1`, so (PI) says that the unit of `R` is properly infinite.

**No exhaustion is asserted.**  `v_0w_0 + v_1w_1 = 1` is not part of (PI)
and does not follow from it; a ring satisfying (PI) need not be isomorphic
to `M_2(R)`.  That is what separates this hypothesis from the prefix-code
situation of `binary-leavitt-all-ranks-full-mf-radical`.
