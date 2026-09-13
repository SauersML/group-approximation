---
rg: 2
id: four-strand-burau-representation-has-nontrivial-kernel
kind: claim
title: Some nontrivial 4-strand braid has identity Burau matrix
distinct_from:
  four-strand-burau-representation-is-faithful: that claim is the Yes answer to Zaremsky Problem 3.5; this claim is the No answer, the existence of a nontrivial kernel element in B_4
---

There is a nontrivial braid `beta` in `B_4` whose Burau matrix is the
identity. This is the No answer to Zaremsky Problem 3.5
(`zaremsky-3-05-four-strand-burau-faithful`).

## Attempts

- Kernel elements for `n = 5` and `n >= 6` come from Bigelow's and
  Long–Paton's criterion: a pair of arcs in the punctured disk whose
  algebraic (Burau) intersection pairing vanishes while they cannot be
  isotoped apart gives a nontrivial kernel element. For `n = 4` no such pair
  was known when the list was written.
- 2026-09-13: deferred. arXiv:2607.05283v1 claims the opposite answer, and
  its argument is being checked first. A bounded search for arc pairs or
  kernel words starts only if that check finds a gap.
