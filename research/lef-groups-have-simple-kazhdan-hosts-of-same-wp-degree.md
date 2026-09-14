---
rg: 2
id: lef-groups-have-simple-kazhdan-hosts-of-same-wp-degree
kind: claim
title: Every finitely generated LEF group is a subgroup of an infinite finitely generated simple Kazhdan expander limit of finite simple groups whose word problem has the same Turing degree
distinct_from:
  lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts: that is the solvable case, an equivalence between solvable word problem of the group and of a host; this fixes the Turing degree of the host's word problem for every finitely generated LEF group, solvable or not, and implies that case.
  lef-groups-embed-in-simple-kazhdan-lef-groups: that characterizes LEF groups as subgroups of simple Kazhdan LEF groups with no control of the host's word problem; this adds that the host's word problem can be made Turing equivalent to the group's.
  every-turing-degree-is-a-simple-kazhdan-lef-word-problem: that realizes each Turing degree by the word problem of some subshift group G_X; this realizes the degree of a given LEF group by a host containing it.
artifacts:
  - simple_kazhdan_sofic_group.tex
---

**ESTABLISHED (proof in the note, revision 5.1; reviewed by main only).** Let `Γ` be a finitely generated LEF group.
Then there is an infinite, finitely generated, simple group `H` with property (T), which is an expander limit of
finite simple groups `SL_N(F_2)` (so LEF, sofic and hyperlinear), such that `Γ ≤ H` and

    WP(Γ) ≤_m WP(H) ≤_T WP(Δ) ≤_T WP(Γ),

so the word problems of `Γ` and `H` have the same Turing degree. In particular `Γ` has solvable word problem if and
only if it is a subgroup of such a host with solvable word problem (`lef-wp-groups-have-decidable-simple-kazhdan-lef-hosts`).

**Host.** `Δ = C(Γ)` is the half-line overgroup, and `H = G_Δ = EL_3(LC(F_2^Δ,F_2) ⋊ Λ)` with `Λ` the lamplighter
group of affine maps `x ↦ δx + c`. This is Corollary 3 of `simple_kazhdan_sofic_group.tex`, revision 5.1
(main 37ebf96798), whose Lemma C states the two reductions and whose corollary proof adds the embedding reduction.

**Origin.** Proposed in an outside referee report on revision 4.5 of the note (2026-09-14), as the relativization of
the solvable-word-problem argument. Main re-derived it: the LEF half of Lemma C never used solvability, the two
decision procedures relativize to an oracle for `WP(Γ)`, and substitution of generator words gives the many-one
reduction. No novelty claim beyond the note is made.

Route: `lef-groups-have-simple-kazhdan-hosts-of-same-wp-degree-proof`.
