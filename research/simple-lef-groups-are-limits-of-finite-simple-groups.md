---
rg: 2
id: simple-lef-groups-are-limits-of-finite-simple-groups
kind: claim
title: An infinite finitely generated simple group is LEF iff it is a marked limit of finite simple groups, and these must have unbounded rank
distinct_from:
  finite-simple-groups-converge-to-simple-kazhdan-group: that builds PSL_3N(F_q) approximants of the subshift groups; this turns ANY finite approximation of ANY infinite simple group into finite simple approximants, and shows their rank is unbounded.
  lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple: that constructs SL_N(F_2) configuration models for the lamplighter hosts; this is the general quotient lemma, which gives finite simple approximants of every simple LEF group without new models.
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part1.md
  - research/artifacts/sk-verify-14-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** Let `G` be an infinite simple group with finite generating set `T`, and
`(Q_k, T_k) → (G, T)` with `Q_k` finite.

1. For large `k` and any maximal normal subgroup `M_k` of `Q_k`, the finite nonabelian simple groups `Q_k/M_k`, with
   the images of `T_k`, still converge to `(G, T)`. So an infinite f.g. simple group is LEF iff it is a marked limit of
   finite simple groups.
2. If `(Q_k, T_k) → (G, T)` with `Q_k` finite simple, then for each `d` only finitely many `Q_k` embed in `GL_d` of a field.
   So by the classification the `Q_k` are eventually alternating of unbounded degree, or of Lie type of unbounded Lie rank.

Why (1) works: each nontrivial ball element `w` normally generates `G`. The finitely many identities
`t = ∏ h_i w^(±1) h_i^(-1)` are relators of bounded length, so they hold in `Q_k`. If `w` fell into `M_k`, every
generator would, and `M_k = Q_k`.

Why (2) works: `G` embeds in `∏_ω Q_k ≤ GL_d(∏_ω K_k)`. A f.g. linear group is residually finite (Mal'cev), and an
infinite simple group is not.

Combined with `kazhdan-marked-limits-eventually-uniform-expanders`: every infinite f.g. simple Kazhdan LEF group is a
marked limit of finite simple groups, and every finite approximation of it eventually expands.

Credit: elementary, and likely folklore (bounded search in artifact part 3).

Route: `simple-lef-groups-are-limits-of-finite-simple-groups-proof`.

**Review (sk-verify-14, 2026-09-13): PASS.** Theorem B re-derived: relators and nonrelators survive quotients by any maximal normal subgroups, uniformly in the choice, and simplicity is used only for normal closures (model test `Z` with `Z/p^a`). Proposition B3 re-derived: ultraproduct, Łoś, Mal'cev. Wording fix F-B3 for the artifact's classification step: use `PGL_m(K) ↪ GL_(m^2)(K)` by conjugation on `M_m(K)`, not the adjoint representation. See `research/artifacts/sk-verify-14-2026-09-13-part1.md` §§2–3.
