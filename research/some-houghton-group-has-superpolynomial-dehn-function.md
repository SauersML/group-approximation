---
rg: 2
id: some-houghton-group-has-superpolynomial-dehn-function
kind: claim
title: "Some Houghton group H_n (n >= 3) has Dehn function exceeding every polynomial"
distinct_from:
  houghton-groups-have-polynomial-dehn-function: that asserts a polynomial bound for every H_n; this is its negation, that some H_n has no polynomial bound.
---

There is `n >= 3` such that for every `d`, `δ_(H_n)(x) ≼ x^d` fails. With
Lee's upper bound (`houghton-groups-have-at-most-exponential-dehn-function`)
the Dehn function would then lie between every polynomial and `e^x`.

## Attempts

- 2026-09-13 (z1-24-houghton): the standard exponential mechanisms are
  absent. `H_n` contains no `BS(1,m)` with `|m| >= 2` (translation vectors
  force `v(a) = m v(a)`), and finitary permutations are at most
  `P log P`-distorted (Burillo–Cleary–Martino–Röver, arXiv:1403.0026,
  Theorem 4.1). A superpolynomial lower bound would need a new mechanism,
  such as areas of commutation relations among transpositions growing
  exponentially in their distance from the origin. No candidate is known.
