---
rg: 2
id: no-decidable-group-contains-every-fp-rf-group
kind: claim
title: No finitely generated group with solvable word problem contains every finitely presented residually finite group
distinct_from:
  no-finitely-generated-group-contains-all-fg-rf-groups: that is the counting obstruction for all finitely generated residually finite groups; this is the computability obstruction for the countable subclass of finitely presented ones.
  recursive-lef-growth-hosts-miss-some-fp-rf-group: that excludes LEF hosts whose finite partial models are recursively bounded; this excludes every host with solvable word problem, LEF or not.
  erf-groups-have-decidable-simple-kazhdan-hosts: that asks for a host with solvable word problem for ONE effectively residually finite group; this rules out one decidable host for ALL finitely presented residually finite groups.
artifacts:
  - research/artifacts/sk-wp-host-2026-09-13.md
---

**ESTABLISHED (unreviewed).** If a finitely generated group `U` contains a copy of every finitely presented
residually finite group, then the word problem of `U` is unsolvable.

In particular the hosts of `universal-simple-kazhdan-lef-groups-exist` and Corollary U′ of
`simple-kazhdan-lef-host-for-countably-many-rf-groups` have unsolvable word problem. So a simple Kazhdan LEF group with
solvable word problem that contains every finitely presented residually finite group does not exist, and the
"computability" target recorded in sk-strong-3's artifact is refuted.

What survives is one host per group, or per family with a uniform complexity bound: see
`erf-groups-have-decidable-simple-kazhdan-hosts` and the questions in the artifact.

DERIVATION
no-decidable-group-contains-every-fp-rf-group-proof

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS, conditional on `uniform-wp-bound-excludes-bh-universal-targets` (§4).

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part3.md`):** PASS, independent concurrence (§4), conditional on `uniform-wp-bound-excludes-bh-universal-targets`. `t(n)` is recursive and `WP(U) ∈ F(t)` with `C = 1`.
