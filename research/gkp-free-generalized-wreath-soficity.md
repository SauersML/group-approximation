---
rg: 2
id: gkp-free-generalized-wreath-soficity
kind: claim
title: A free generalized wreath product over a sofic set action is sofic
distinct_from:
  gkp-wreath-permanence-theorem: that imports Theorem 3.6 for restricted direct-sum lamps; this imports Theorem 3.7 for free-product lamps indexed by the same action
  gkp-sofic-action-toolkit: that imports the set-action permanence results from Section 2; this imports the free generalized wreath-product consequence from Section 3
---

**Literature input (source re-read 2026-08-31, arXiv:2401.04945v3
HTML).**  Gao--Kunnawalkam Elayavalli--Patchell, *Soficity for group
actions on sets and applications*, Res. Math. Sci. 12 (2025), 48,
arXiv:2401.04945, Definition 3.2 and Theorem 3.7.

Let `K` and `H` be countable sofic groups, and let
`alpha:H action X` be a sofic action on a countable set.  Then

```text
K wr^*_alpha H := (*_(x in X) K_x) rtimes H
```

is sofic, where `H` permutes the free factors through `alpha`.

This is the `A={1}` specialization of the paper's stronger Theorem 3.7.
That theorem treats

```text
(*_(x in X; amalgamated over A) K_x) rtimes H
```

provided the free amalgam of any countable number of copies of `K` over
`A` is sofic.  Its stated corollaries include the free case above and the
case of amenable `A`.

The same paper gives a Hilbert--Schmidt analogue: Corollary 3.10 says that if
`K,H` are hyperlinear and `alpha` is a sofic action, then the free
generalized wreath product is hyperlinear.  The group-sofic conclusion above
is stronger in the application to one-compressor Kun--Thom doubles.
