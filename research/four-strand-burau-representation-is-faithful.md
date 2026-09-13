---
rg: 2
id: four-strand-burau-representation-is-faithful
kind: claim
title: The Burau representation of the 4-strand braid group is faithful
distinct_from:
  four-strand-burau-representation-has-nontrivial-kernel: that claim is the opposite answer to Zaremsky Problem 3.5, a nontrivial 4-braid with identity Burau matrix; this claim is injectivity of the Burau homomorphism on B_4
artifacts:
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part1.md
  - research/artifacts/zp-burau-n4-verification-2026-09-13-part2.md
---

The Burau homomorphism `B_4 -> GL_4(Z[t, t^{-1}])` (equivalently its reduced
3-dimensional version) is injective. This is the Yes answer to Zaremsky
Problem 3.5 (`zaremsky-3-05-four-strand-burau-faithful`).

## Attempts

- arXiv:2607.05283v1 (Bharathram–Birman–Brendle, July 6, 2026, unrefereed)
  claims this theorem.
  - Check by z3-05-burau-search, 2026-09-13: GAP, so no citation route.
    Gaps G1–G6 are in
    `research/artifacts/zp-burau-n4-verification-2026-09-13-part2.md`.
  - The decisive gap is the last step of Proposition 6.4: parity of the
    modified push map `Gamma'`, and the strict increase of
    `iota(alpha, (beta_*^3)Gamma')`, are asserted without proof.
  - The preprint's strategy is recorded as the route
    `four-strand-burau-faithful-via-parity-correction`. It requires the open
    claim `brunnian-four-braids-admit-parity-correcting-push`.
