---
rg: 2
id: lef-iff-subgroup-of-simple-kazhdan-all-approximants-expand
kind: claim
title: A f.g. group is LEF iff it lies in an infinite simple Kazhdan limit of finite simple groups all of whose finite approximations expand
distinct_from:
  lef-iff-subgroup-of-simple-kazhdan-limit-of-finite-simple: that builds SL_N(F_2) configuration models for the lamplighter hosts, and gets expansion for those markings; this derives the headline from the LEF host alone through two general lemmas, with expansion for EVERY approximating sequence and marking, but no control of the type of the finite simple groups.
artifacts:
  - research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part1.md
  - research/artifacts/sk-verify-14-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).** For a finitely generated group `Γ` the following are equivalent.

1. `Γ` is LEF.
2. `Γ` is a subgroup of an infinite finitely generated simple Kazhdan group `G` that is a marked limit of finite simple
   groups, and such that, for every finite generating set `T` of `G`, every sequence of finite marked groups converging
   to `(G, T)` is eventually a family of expanders.

For the note: once Corollary 2 (the simple Kazhdan LEF host) is proved, this form of the unified headline costs about
six lines and one citation (Shalom's openness of (T)). The configuration models are needed only to name `SL_N(F_2)` as
the approximants.

Route: `lef-iff-subgroup-of-simple-kazhdan-all-approximants-expand-proof`.

**Review (sk-verify-14, 2026-09-13): PASS.** Both directions re-derived from the reviewed LEF host `lef-groups-embed-in-simple-kazhdan-lef-groups` and the two lemmas it requires. See `research/artifacts/sk-verify-14-2026-09-13-part1.md` §4.
