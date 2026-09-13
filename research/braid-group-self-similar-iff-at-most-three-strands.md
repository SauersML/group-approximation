---
rg: 2
id: braid-group-self-similar-iff-at-most-three-strands
kind: claim
title: The braid group B_n is self-similar if and only if n <= 3
distinct_from:
  braid-groups-on-at-most-three-strands-are-self-similar: that is the positive half, a construction for n <= 3; this is the full classification, which also needs the negative half for n >= 4.
  braid-groups-on-four-or-more-strands-are-not-self-similar: that is the negative half for n >= 4; this is the full classification, which also needs the construction for n <= 3.
---

For `n >= 1`, the braid group `B_n` has a faithful state-closed action on some
rooted regular tree `T_d` if and only if `n <= 3`. Here "self-similar" is
Zaremsky's definition from arXiv:2405.09722, with no transitivity assumed.

This is the answer claim for the first part of Zaremsky Problem 3.9, "Are braid
groups self-similar?"; see `zaremsky-3-09-braid-groups-self-similar`. It
follows from the two halves through
`braid-self-similarity-from-small-and-large-cases`.
