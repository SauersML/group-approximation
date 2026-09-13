---
rg: 2
id: four-strand-burau-representation-has-nontrivial-kernel
kind: claim
title: Some nontrivial 4-strand braid has identity Burau matrix
distinct_from:
  four-strand-burau-representation-is-faithful: that claim is the Yes answer to Zaremsky Problem 3.5; this claim is the No answer, the existence of a nontrivial kernel element in B_4
artifacts:
  - research/artifacts/zp-burau-k4-kernel-search-2026-09-13.md
---

There is a nontrivial braid `beta` in `B_4` whose Burau matrix is the
identity. This is the No answer to Zaremsky Problem 3.5
(`zaremsky-3-05-four-strand-burau-faithful`).

## Attempts

- **Known mechanism.** For `n = 5` and `n >= 6`, kernel elements come from
  the criterion of Bigelow and Long–Paton. Find a pair of arcs in the
  punctured disk whose algebraic (Burau) intersection pairing vanishes, while
  the arcs cannot be isotoped apart; this gives a nontrivial kernel element.
  For `n = 4` no such pair was known when the list was written.
- **2026-09-13, exhaustive search** (lane z3-05-burau-search, MSI).
  - Kernel elements that matter lie in the point-pushing subgroup `K_4`
    (Long's theorem). Meet-in-the-middle enumeration over all reduced words
    of length at most 12 in `A_{14}, A_{24}, A_{34}` and their inverses
    found no kernel element of free length at most 24.
  - Established as `burau-kernel-avoids-short-point-pushing-braids`.
  - Any kernel element in `K_4` therefore has free length at least 26.
  - Length 26 needs about 70 GB in the present layout; going beyond needs a
    disk-backed sort or a split by first letter. Growth is `5^L`, so this
    search route is not expected to decide the problem.
- **Where it stands.** arXiv:2607.05283v1 claims the opposite answer; the
  check found a gap in its `n = 4` core (see
  `four-strand-burau-representation-is-faithful`). A kernel element would
  have to defeat the parity mechanism of that preprint. For a braid in the
  kernel, the unproved step G1 of Proposition 6.4 must fail, so the choice of
  `gamma''` there is the natural place to look for Moody-type arc pairs with
  vanishing pairing.
