---
rg: 2
id: smart-induced-map-has-brick-local-height-3-renormalization
kind: claim
title: The induced SMART element of 2V has a brick-local height-3 renormalization, deleting one cell next to the head
distinct_from:
  smart-level-zero-return-map-factors-onto-3-adic-odometer: that gives the 3-adic odometer factor; this gives the brick-local conjugacy of U^3 on one tower level to U, which is strictly more.
  smart-induced-on-genuine-moves-has-exact-tripling: that counts 3^k steps per level-k move; this identifies each level-(k+1) move with a level-k move by one bounded edit.
  renormalizable-thompson-elements-give-baumslag-solitar: that turns a renormalization into BS(1,m); this supplies one with m = 3.
artifacts:
  - research/artifacts/gq-gq-nv-obstruct-smart-renormalization.md
  - research/artifacts/gq-affq-smart-renormalization-search.md
  - research/artifacts/gq-affq-smart-renormalization-validation.md
---

**OPEN (proof claimed 2026-09-18, under review by gq-referee-a and gq-referee-b; numerical check by gq-affq passed, cba5854a6).** Lane gq-nv-obstruct. Full proof in the artifact.

**Statement.** Let `U = F_Y ∈ 2V`, SMART's moving-tape map induced on its genuine level-0 moves
(`smart-induced-on-genuine-moves-has-exact-tripling`), up to brick-local conjugacy. Let
`A ⊆ Y` be the first `Y`-points of level-1 moves. Then:
- `Y = A ⊔ UA ⊔ U^2A`;
- the map `φ: A → Y` is a brick-local homeomorphism with `φ ∘ U^3 = U ∘ φ` on `A`.

`φ` has four cases:
- at a start of `M_b(1)`, delete the `0` right of the head;
- at a start of `M_d(1)`, delete the `0` left of the head;
- at the first `Y`-point of `M_p(1)` (`b_2` on the written `2`), delete the head cell, move the head
  left, and change the state to `p_2`;
- the `M_q(1)` case is the mirror of the `M_p(1)` case.

**Why it works.** By induction on the level, with Callard–Salo's `prop:smart-moves`, `M_x(K)` at the start of
its `ρ`-th level-1 sub-move is `M_x(K-1)` at the start of its `ρ`-th level-0 sub-move, plus one cell in
the innermost 3-cell region. The extra cell and the junction-written boundary values do not depend on
the level.
- **Where the identity holds.** It holds directly wherever `y` and `U^3 y` share a finite-level move.
- **Everywhere else.** Those points are dense: failures need an all-`p` or all-`q` ancestor chain, which
  one far-away cell edit breaks. So the identity holds everywhere by continuity.

**Note on gq-affq's search.** A deletion next to the head is a bounded prefix replacement. That applies
to `P(b_2,c_0)D(0) → P(b_2,c_0)` as much as to any move of `F`. So the structural objection in
`gq-affq-smart-renormalization-search.md` §4 does not apply to this `φ`. That search's measured
failure used a materialised window `W = 120`, smaller than its equality radius `R_EQ = 150`. It also
searched deletions only, whereas the `p` and `q` cases also change the state.

**If it survives review.** `renormalizable-thompson-elements-give-baumslag-solitar` gives `BS(1,3) <= 3V`
(`bs13-embeds-in-brin-thompson-3v`).

**Numerical validation** by gq-affq (MSI, cba5854a6, `research/artifacts/gq-affq-smart-renormalization-validation.md`):
- 55,000 checks of `φ S^3 = S φ`, none failed. Each compares whole finite tape arrays relative to the head.
- The tape densities tested are `P(0) = 1/3, 0.5, 0.9, 0.97`.
- The tower period is exactly 3.
- The explicit inverse passes 8,069 checks.
- gq-affq retracted §4 of its search artifact: deleting the head's neighbour is a prefix replacement. The
  radius-150 "collapse" was a harness artefact.

**Review.**
- gq-referee-b (citation and hypothesis lens): **PASS**. Report
  `research/artifacts/gq-referee-b-smart-induced-map-has-brick-local-height-3-renormalization.md` (b6d33ae8e).
  - It reviewed `renormalizable-thompson-elements-give-baumslag-solitar` in full, so that criterion needs
    no separate review on this lens.
  - Items 1–3 are met with `k = 2`, `m = 3`.
  - Its wording fixes W1–W3 are applied: infinite order is cited from the aperiodicity of `F`, the lemma's
    two senses of `content` are separated, and the distortion and priority claims are toned down.
- gq-referee-a (proof-gap lens): **PASS**, report 12b5beb4a. It re-derived the first-`Y`-point table, the
  level-independence of the extra-cell side and of `β`, the identity, the density argument (a failure is
  exactly an all-`p` or all-`q` chain), and the brick-locality of `φ` after transport by `ψ`.
- Priority check: requested from gq-lit-arxiv.
