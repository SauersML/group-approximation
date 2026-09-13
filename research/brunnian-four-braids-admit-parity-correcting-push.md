---
rg: 2
id: brunnian-four-braids-admit-parity-correcting-push
kind: claim
title: Every nontrivial Brunnian 4-braid has a conjugate and a 5-strand push map giving parity-clean arcs with unequal intersection counts
artifacts:
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part1.md
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part2.md
---

Let `alpha` be the arc from `p1` to `p2` and `beta_*^3` the standard arc from
the boundary basepoint to `p3`, and let `f: B_4 -> B_5` be the standard
inclusion. For every nontrivial `Phi` in the Brunnian subgroup `Brun_4` there
are `y` in `B_4` and `Gamma` in `B_5` with the following property. Write
`Phi_1 = y Phi y^{-1}`, `A = (beta_*^3) f(Phi_1) Gamma` and
`B = (beta_*^3) Gamma`. Then representatives of `A` and `B` transverse to
`alpha` both satisfy the **parity condition**: a disk in the disk sequence is
sign-changing iff it contains an odd number of marked points. Moreover
`|A ∩ alpha| != |B ∩ alpha|`.

This packages Proposition 6.4, Corollary 6.5 and the conjugation step of
Theorem 6.6 of arXiv:2607.05283v1 (Bharathram–Birman–Brendle). By the route
`four-strand-burau-faithful-via-parity-correction`, it implies that the
Burau representation of `B_4` is faithful.

## Attempts

- arXiv:2607.05283v1, Section 6: conjugate `Phi` into a proper product
  `Phi'.Gamma_1`, list the possible disk types (Lemma 6.3), then build
  `Gamma = gamma_2 ∘ gamma_1` to turn 4-disks into 5-disks.
  - Status (z3-05-burau-search, 2026-09-13): not verified.
  - Proposition 6.4's final step replaces `gamma_2` by
    `gamma' ∪ gamma'' ∪ gamma_2` and asserts two facts without proof: that
    the intersection count strictly increases, and that the new loop still
    satisfies parity.
  - Lemmas 6.2–6.3 are supported by figures only.
  - The normalization "a freely reduced product is a proper product" is not
    proved.
  - Details: `research/artifacts/zp-burau-n4-verification-2026-09-13-part2.md`,
    gaps G1–G6.
- **Where it stands.** For a braid in the kernel, the two unproved facts in
  G1 contradict each other. So this claim is no easier than the theorem for
  that braid, and a proof must choose `gamma''` with control over the new
  disk types.
