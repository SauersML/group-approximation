---
rg: 2
id: lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple
kind: claim
title: A finitely generated group is LEF iff it is a subgroup of an infinite simple Kazhdan group that is a marked limit of finite simple expanders SL_3N(F_2)
distinct_from:
  lef-groups-embed-in-simple-kazhdan-lef-groups: that gives a simple Kazhdan LEF host; this shows the same host is a limit, in the space of marked groups, of the finite simple groups SL_{3N}(F_2), whose Cayley graphs form expanders.
  finite-simple-groups-converge-to-simple-kazhdan-group: that is the marked convergence for the subshift groups G_X over Z; this is the convergence for the lamplighter hosts, which contain every finitely generated LEF group.
---

**ESTABLISHED (unreviewed).** For a finitely generated group `Γ` the following are equivalent.

1. `Γ` is LEF.
2. `Γ` is a subgroup of an infinite, finitely generated, simple group `G` with property (T) and a finite generating
   set `S_G` such that, for a sequence `N_k → ∞`, the marked groups `(SL_(3N_k)(F_2), images of S_G)` converge to
   `(G, S_G)` in the space of marked groups, and their Cayley graphs form a family of expanders.

In words: **the finitely generated LEF groups are exactly the subgroups of infinite simple Kazhdan groups that are
limits of finite simple expanders.** This is the host-level form of `lef-groups-embed-in-simple-kazhdan-lef-groups`, and
it matches the headline object of `simple_kazhdan_sofic_group.tex`, where `G_X` is such a limit.

**The host.** Take `Γ ≤ [Δ,Δ]` with `Δ` finitely generated, infinite and LEF. Let `L = Z/2 ≀ Δ` act on `Y = 2^Δ`,
`R = LC(Y,F_2) ⋊ L` and `G = EL_3(R)` (`lamplighter-bernoulli-crossed-products-simple-kazhdan-lef`). The only new point
is the choice of finite models. They live on the configuration spaces `2^(Q_n)` of the LEF models `Q_n` of `Δ`, not on
`2^(Q_n) × Q_n`. There the generator images generate the full matrix algebra `M_(2^|Q_n|)(F_2)`.

Route: `lef-iff-subgroup-of-simple-kazhdan-limit-finite-simple-proof`. The full derivation is in
`research/artifacts/sk-strong-6-envelope-table-2026-09-13.md` §2.

**Review (sk-verify-7, 2026-09-13, `research/artifacts/sk-review-7-2026-09-13-part3.md`):** PASS: view models, covariance, nonvanishing, surjectivity, marked limit and expansion re-derived (§1). Duplicate D1: sk-strong-6's `lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple` and sk-strong-8's `lef-iff-subgroup-of-simple-kazhdan-finite-simple-limit` state the same theorem, so one should subsume the other.
