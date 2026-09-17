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
- **2026-09-17, exhaustive Bigelow arc-pair search** (sw-094, flagship-2026-09-17, curve-pair-enumeration).
  - The search enumerates every minimal-position arc `alpha` from `q_1` to `q_2` on `D_4` by its crossing sequence against the arc `beta_0` from `p_0` to `q_3`, then tests the exact pairing polynomial.
  - No pair with `i <= 250` has vanishing pairing. This is established as `no-four-strand-bigelow-arc-pair-with-at-most-250-crossings`.
  - By Bigelow's criterion, a kernel element must have a conjugate that pushes `alpha_0` across `beta_0` more than 250 times.
  - Controls: two independent implementations agree on leaf counts; `n = 3` shows no cancellation for `m <= 40`; `n = 6` has hits at `m = 8`.
  - Cost grows like `M^{5.3}`, so reaching Bigelow's asserted 500 would cost about 40 times this run.
  - Near-miss families have `||p||_1 = 6`, with blocks divisible by `1 - t + t^2`, so no norm-growth obstruction is visible. The next lever is the Brunnian reduction: restrict to arcs that become trivial in `D_3` once `q_4` is filled. Those grow only like `m^2` per `m`, which makes a reverse search past 500 plausible.
