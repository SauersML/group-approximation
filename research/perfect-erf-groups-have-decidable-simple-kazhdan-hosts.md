---
rg: 2
id: perfect-erf-groups-have-decidable-simple-kazhdan-hosts
kind: claim
title: Every finitely generated infinite perfect effectively residually finite group with solvable word problem embeds in an infinite simple Kazhdan LEF group with solvable word problem
distinct_from:
  rf-groups-embed-in-simple-kazhdan-lef-groups: that embeds every finitely generated residually finite group, with no control on the word problem of the envelope; this makes the envelope's word problem solvable, which forces effective residual finiteness and a copy inside a derived subgroup.
  simple-kazhdan-lef-hosts-all-countable-locally-finite: that hosts every countable locally finite group in one envelope, with no control on the word problem; this controls the word problem of the envelope, for one group at a time.
artifacts:
  - research/artifacts/sk-wp-embedding-decidable-envelopes-2026-09-13.md
---

**ESTABLISHED (unreviewed).** Let `Γ` be finitely generated and infinite with `Γ ≤ [Δ,Δ]` for some finitely
generated infinite `Δ` that is effectively residually finite with solvable word problem. Then `Γ` embeds in an
infinite, finitely generated, simple group with property (T) that is LEF, hence sofic and hyperlinear, and whose
word problem is solvable. The envelope is `EL_3(LC(X_Δ,F_2) ⋊ Δ)` for the Toeplitz subshift `X_Δ` of the chain.

**Corollary (perfect groups).** Taking `Δ = Γ`: every finitely generated infinite perfect effectively residually
finite group with solvable word problem embeds in an infinite finitely generated simple Kazhdan LEF group with
solvable word problem. This covers `SL_n(Z)` for `n ≥ 3` and every finitely presented perfect residually finite
group, since finite presentation with residual finiteness gives effective residual finiteness and a solvable word
problem.

**Converse.** A finitely generated subgroup of a finitely generated group with solvable word problem has solvable
word problem, and a subgroup of a LEF group is LEF. So every group with such an envelope is LEF with solvable word
problem. It need not be residually finite: `[[T]]'` of a computable minimal subshift embeds in the manuscript's own
`G_X` by `topological-full-group-embeds-in-subshift-elementary-group`, is LEF and is not residually finite.

**Sharpness.** Effective residual finiteness cannot be weakened to residual finiteness with solvable word problem:
by Rauzy's Theorem 2, imported in `rf-higman-embedding-for-decidable-groups-fails`, the two are different.

**Correction to the sharpness remark (sk-decidable-host, 2026-09-13).** The two hypotheses differ, but the conclusion
survives the weakening. `lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts` (unreviewed) gives an infinite
finitely generated simple Kazhdan LEF host with solvable word problem for every finitely generated LEF group with
solvable word problem. So it gives one for every finitely generated residually finite group with solvable word
problem, effective or not, and with no derived-subgroup hypothesis. Effective residual finiteness is sharp only for
this node's route through Toeplitz subshifts and residually finite overgroups.

Route: `perfect-erf-groups-have-decidable-simple-kazhdan-hosts-proof`.

**Review (sk-verify-4, 2026-09-13): PASS.** Computable chain, computable Toeplitz subshift, Corollary T, the `[Δ,Δ]` embedding and the degree formula composed; the `SL_n(Z)` corollary and the converse checked. See `research/artifacts/sk-review-4-2026-09-13-part5.md` §4.
