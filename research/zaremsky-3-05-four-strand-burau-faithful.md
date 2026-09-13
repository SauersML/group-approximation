---
rg: 2
id: zaremsky-3-05-four-strand-burau-faithful
kind: claim
title: "Zaremsky Problem 3.5 resolved: is the 4-strand Burau representation faithful?"
root: true
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3 ("Matrix groups,
braid groups, etc"), Problem 5, verbatim: "Is the 4-strand Burau
representation faithful?"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-05-by-yes` requires
  `four-strand-burau-representation-is-faithful`.
- **No**: `zaremsky-3-05-by-no` requires
  `four-strand-burau-representation-has-nontrivial-kernel`.

Never write a `requires: []` route into this claim.

**Reading.** The Burau representation of the braid group `B_n` sends the
standard generator `sigma_i` to the matrix acting as
`[[1-t, t], [1, 0]]` on coordinates `i, i+1` and as the identity elsewhere,
giving `B_n -> GL_n(Z[t, t^{-1}])`; it splits off a trivial summand over
`Q(t)`, and the reduced and unreduced versions have the same kernel. The
question asks whether this homomorphism is injective for `n = 4`.

**Known before the list.** Faithful for `n <= 3` (Magnus–Peluso, 1969).
Not faithful for `n >= 9` (Moody, 1991), for `n >= 6` (Long–Paton, 1993),
and for `n = 5` (Bigelow, 1999). The list (July 12, 2026) records `n = 4`
as open.

## Attempts

- 2026-09-13: arXiv:2607.05283v1 (V. Bharathram, J. S. Birman, T. E.
  Brendle, "The Burau representation of the braid group is faithful for
  n = 4", posted July 6, 2026, 26 pages, unrefereed, no later version or
  withdrawal as of September 13, 2026) claims the Yes answer, using ideas of
  Moody, Long, Long–Paton and Bigelow. A line-by-line check of that argument
  is in progress (artifact `research/artifacts/zp-burau-n4-verification-2026-09-13*.md`
  once landed). Neither answer route is complete until that check lands.
