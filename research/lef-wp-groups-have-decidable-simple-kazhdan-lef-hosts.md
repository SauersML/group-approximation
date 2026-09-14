---
rg: 2
id: lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts
kind: claim
title: A finitely generated group is LEF with solvable word problem iff it is a subgroup of an infinite finitely generated simple Kazhdan LEF group with solvable word problem
distinct_from:
  perfect-erf-groups-have-decidable-simple-kazhdan-hosts: that needs the group inside the derived subgroup of an effectively residually finite overgroup with solvable word problem, and uses Toeplitz subshifts; this needs only LEF with solvable word problem, uses the half-line overgroup and the lamplighter host, and is an equivalence.
  lef-groups-embed-in-simple-kazhdan-lef-groups: that characterizes LEF groups with no control of the host's word problem; this characterizes LEF groups with solvable word problem through hosts with solvable word problem.
  no-decidable-group-contains-every-fp-rf-group: that rules out one decidable host for all finitely presented residually finite groups; this gives one decidable host for each group.
artifacts:
  - research/artifacts/sk-decidable-host-2026-09-13.md
  - research/artifacts/sk-verify-14-2026-09-13-part3.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be a finitely generated group. Then `Γ` is LEF with solvable word problem if and
only if `Γ` is a subgroup of an infinite, finitely generated, simple group with property (T) that is LEF and has
solvable word problem.

**Host.** Take `Δ = C(Γ)`, the half-line overgroup, which is LEF with `WP(Δ) ≡_T WP(Γ)` and `Γ ≤ [Δ,Δ]`. The host is
`G = EL_3(LC(2^Δ, F_2) ⋊ (Z/2 ≀ Δ))`, the lamplighter host of the note's Corollary 2 over `Δ`, and
`WP(G) ≤_T WP(Δ)`.

**Consequences.**
- Every finitely generated residually finite group with solvable word problem has such a host, whether or not it is
  effectively residually finite in Rauzy's sense. So `erf-groups-have-decidable-simple-kazhdan-hosts` holds, through
  `erf-groups-decidable-hosts-via-half-line-proof`.
- Examples: `SL_n(Z)` for `n ≥ 3`, every finitely presented residually finite group, every f.g. linear group over a
  field with computable arithmetic, and the note's `G_X` for recursive `L(X)`.

**Credit.** Boone–Higman (1974) and Thompson (1980): a f.g. group has solvable word problem iff it embeds in a
finitely generated simple group with solvable word problem. This is the analogue inside LEF groups, with (T).

Route: `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts-proof`.

**Review (sk-verify-14, 2026-09-13): PASS.** Re-derived: both directions; the subshift model `F_x(ℓ) = (ℓ^(-1)x)(e)` of the lamplighter action; `WP(L) ≤_T WP(Δ)` by lamp parities; and `L(X) ≤_T WP(Δ)` by consistency of the constraints `x(δ_w) = p(w) + c_w(δ_w)`. The inputs carry PASS reviews: the lamplighter host (three) and the word-problem formula (sk-verify-4). Thompson's 1980 locator is not checked. See `research/artifacts/sk-verify-14-2026-09-13-part3.md` §4.
