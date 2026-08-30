---
rg: 2
id: sofic-quotient-nonclosure
kind: claim
title: Soficity fails under a finite-relator quotient of the rank-two free group
distinct_from:
  mf-quotient-nonclosure: that concerns operator-MF and uses a rank-eight free source; this concerns soficity and has rank-two free source with finitely normally generated kernel.
  finitely-presented-nonsofic-group-exists: that constructs a finitely presented nonsofic target; this records the quotient-permanence consequence and strengthens it to a fixed two-generator target.
  hyperlinear-quotient-permanence-equivalence: arbitrary hyperlinear quotient permanence remains equivalent to universal hyperlinearity; arbitrary sofic quotient permanence is false.
  local-approximation-properties-are-marked-closed: hereditary and marked-closed do not imply quotient permanence; the finite-obstruction cover proves nonsoficity directly.
artifacts:
  - GroupApproximation/Endpoint/MainResults.lean
---

There are a finitely normally generated normal subgroup `N ◁ F_2` and a
fixed two-generator finitely presented group `V = F_2/N` such that

```text
F_2 is sofic,
V is nonsofic.
```

Equivalently, there is one fixed finite presentation

```text
V = <a,b | r_1,...,r_m>
```

whose presented group is nonsofic. Thus sofic groups are not closed under
quotients, even when the source is the rank-two free group and the kernel is
the normal closure of finitely many fixed relators.

**ESTABLISHED 2026-08-30** by
[[sofic-quotient-nonclosure-via-universal-test-group]].
