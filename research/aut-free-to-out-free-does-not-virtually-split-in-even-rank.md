---
rg: 2
id: aut-free-to-out-free-does-not-virtually-split-in-even-rank
kind: claim
title: For every even rank at least four the projection Aut(F_n) to Out(F_n) admits no section over a finite-index subgroup
distinct_from:
  birman-exact-sequence-does-not-virtually-split: that is the closed-surface Birman sequence of Chen--Salter; this is the free-group extension by inner automorphisms, the analogue main records as open.
  aut-out-free-abelianized-extension-splits-rationally: that shows rational cohomology pulled back from Out(F_n) cannot obstruct a virtual section; this asserts that no virtual section exists in even rank.
  free-splitting-compatible-aut-lifts-are-virtual-sections: that reduces splitting-compatible embeddings into larger rank to virtual sections; this asserts those sections do not exist, which kills that family of embeddings in even rank.
artifacts:
  - research/artifacts/solve-bh-mcg-outfn-2026-09-13.md
---

**OPEN.** For every `g ≥ 2` there is no finite-index `Γ ≤ Out(F_{2g})` with a
homomorphism `Γ → Aut(F_{2g})` lifting the inclusion.

**Why it matters for Boone--Higman.**
- **Lifting constructions.** Every construction in Attempts 1 and 6 of
  `out-free-groups-virtually-embed-in-aut-free-groups` is a virtual section
  (`outer-covering-lifts-are-virtual-sections`,
  `free-splitting-compatible-aut-lifts-are-virtual-sections`). This claim would
  exclude all of them in even rank.
- **What would remain.** Only exotic faithful actions of finite-index subgroups on
  free groups.
- **Rank two.** The sequence does virtually split, since `Out(F_2) ≅ GL_2(Z)` is
  virtually free (`low-rank-out-free-groups-embed-in-aut-free-groups`).

**Route.** `even-rank-aut-out-nonsplitting-via-punctured-birman`, from
`once-punctured-birman-sequence-does-not-virtually-split`.

**Odd rank.**
- **Where odd rank comes from.** Dehn--Nielsen--Baer gives odd rank only through
  bases with `k ≥ 2` punctures, or through non-orientable surfaces.
- **Why it doesn't transfer.** Pushing one puncture past another gives a free push
  group, and on a non-orientable closed surface `H^2(·;Q) = 0`. So the
  diagonal-class contradiction of Chen--Salter's Section 3 has no direct analogue
  there.
