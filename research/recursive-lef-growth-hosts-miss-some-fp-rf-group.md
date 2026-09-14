---
rg: 2
id: recursive-lef-growth-hosts-miss-some-fp-rf-group
kind: claim
title: A finitely generated LEF group with recursively bounded LEF growth misses some finitely presented residually finite group
distinct_from:
  uniform-wp-bound-excludes-bh-universal-targets: that excludes hosts through a recursive bound on word-problem time; this excludes LEF hosts through a recursive bound on the orders of their finite partial models, a hypothesis that does not presuppose a solvable word problem.
  no-finitely-generated-group-contains-all-fg-rf-groups: that is the counting obstruction for all finitely generated residually finite groups; this concerns the countable class of finitely presented ones, which one simple Kazhdan LEF group does contain.
  subshift-elementary-group-lef-growth-complexity-bounds: that bounds the LEF growth of the groups G_X; this is an obstruction for hosts, in terms of their LEF growth.
artifacts:
  - research/artifacts/sk-wp-host-2026-09-13.md
---

**ESTABLISHED (unreviewed).** For a finitely generated group `U = ⟨T⟩` let `L_U(r)` be the least order of a finite
group `Q` with an injective map `φ: B_U(r) → Q` such that `φ(gh) = φ(g)φ(h)` whenever `g, h, gh ∈ B_U(r)`
(Bradford's LEF growth; `L_U(r)` is finite for every `r` if and only if `U` is LEF).

(a) If `U` is LEF and `L_U ≤ h` for some recursive function `h`, then some finitely presented residually finite group
does not embed in `U`.

(b) So every finitely generated LEF group that contains every finitely presented residually finite group has LEF
growth bounded by no recursive function. This applies to the hosts of `universal-simple-kazhdan-lef-groups-exist`
and to Corollary U′ of `simple-kazhdan-lef-host-for-countably-many-rf-groups`.

(c) A finitely generated LEF group with solvable word problem has recursive `L_U`, so by (a) it does not contain every
finitely presented residually finite group. That conclusion also follows, for every host with solvable word problem,
from `no-decidable-group-contains-every-fp-rf-group`. The content of (a) is that it needs no decidability, only a
recursive bound on the finite models.

The key inequality: for a finitely presented subgroup `Γ` of `U`, the depth function of `Γ` is at most `L_U(Cn)`
for large `n`, because partial models of a large ball of a finitely presented group extend to genuine homomorphisms.

DERIVATION
recursive-lef-growth-hosts-miss-some-fp-rf-group-proof

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS: Steps 1-6 re-derived; conditional on the KMS Theorem 4.19 import (§4).

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part3.md`):** PASS, independent concurrence (§4), conditional on the KMS Theorem 4.19 import. Steps 1–6 re-derived, including extension of partial models past the relator length and `ρ_Γ(n) ≤ L_Γ(n) ≤ L_U(Cn) ≤ h(n²)`, with a fixed generating set.
