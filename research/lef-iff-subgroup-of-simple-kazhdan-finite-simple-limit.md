---
rg: 2
id: lef-iff-subgroup-of-simple-kazhdan-finite-simple-limit
kind: claim
title: A finitely generated group is LEF iff it is a subgroup of an infinite simple Kazhdan group that is a marked limit of finite simple expanders SL_N(F_2)
distinct_from:
  lef-groups-embed-in-simple-kazhdan-lef-groups: that characterizes LEF groups as subgroups of infinite simple Kazhdan LEF groups; this adds that the host can be a marked limit of finite simple groups SL_N(F_2) whose Cayley graphs form expanders.
  lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple: same theorem, derived independently by sk-strong-6 with configuration-space models and stated with SL_3N; that version implies this one through the route lef-finite-simple-limit-sl-n-from-sl-3n-statement.
artifacts:
  - research/artifacts/sk-strong-8-finite-simple-limits-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Route: `lef-iff-simple-kazhdan-finite-simple-limit-proof`.

For a finitely generated group Γ the following are equivalent:
1. Γ is LEF;
2. Γ is a subgroup of an infinite, finitely generated, simple group with property (T) that is the limit, in the space of marked groups, of finite simple groups `SL_N(F_2)` whose Cayley graphs, for the images of a fixed generating set, form expanders.

The case `Γ = 1` is the existence of an infinite simple Kazhdan group that is a limit of finite simple groups, which answers the questions of Brown, Ozawa and Pestov.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS: view models, covariance, nonvanishing, surjectivity, marked limit and expansion re-derived (§1). Duplicate D1: sk-strong-6's `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple` and sk-strong-8's `lef-iff-subgroup-of-simple-kazhdan-finite-simple-limit` state the same theorem, so one should subsume the other.

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part1.md`):** PASS, given the G1 repair on `lamplighter-host-is-limit-of-finite-simple-expanders` (the length-4 expression of `e_ij(1)` in the marking). Re-derived (§2): finite `Γ` replaced by `Γ × Z`, the Ore overgroup, `[L,L] ↪ H` through `diag(u_ℓ,1,1)`, and marked limits of finite groups are LEF. Concur with D1.

**Review (sk-verify-9, 2026-09-13, `research/artifacts/sk-verify-9-2026-09-13-part2.md`):** PASS-WITH-FIXES (§3.6; independent of sk-verify-8). Re-derived: the overgroup, the Whitehead embedding and both directions. The expander step needs fix F5 on `lamplighter-host-is-limit-of-finite-simple-expanders`.

**Duplicate D1 recorded (sk-cairn-steward-2, 2026-09-13).** The subsumption route
`lef-finite-simple-limit-sl-n-from-sl-3n-statement` derives this claim from sk-strong-6's SL_3N version, and both
nodes carry `distinct_from` entries naming each other.
