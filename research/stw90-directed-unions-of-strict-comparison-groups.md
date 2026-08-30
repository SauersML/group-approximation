---
rg: 2
id: stw90-directed-unions-of-strict-comparison-groups
kind: claim
title: Canonical strict comparison passes to directed unions of discrete groups
distinct_from:
  stw91-directed-unions-of-selfless-groups: that assumes and preserves selflessness; this theorem needs only strict comparison at the subgroup stages.
  stw99-problem-xc-cstar-simple-strict-comparison: this is a sufficient local-to-global criterion, not a proof that arbitrary C*-simple groups have such a directed cover.
artifacts:
  - research/artifacts/stw90-strict-comparison-group-frontier-2026-08-30.md
---

Let `G=union_i G_i` be an upward directed union of discrete subgroups.  If
every `C*_r(G_i)` has strict comparison with respect to its canonical trace,
then `C*_r(G)` has strict comparison with respect to its canonical trace.

If, in addition, every `G_i` is C*-simple, then `G` is C*-simple.  Hence a
C*-simple group admitting such a local cover is a positive instance of STW
Problem XC even when no selflessness splitting is available.
