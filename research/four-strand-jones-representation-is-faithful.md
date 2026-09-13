---
rg: 2
id: four-strand-jones-representation-is-faithful
kind: claim
title: "The Jones representation of the 4-strand braid group is faithful"
distinct_from:
  four-strand-burau-representation-is-faithful: that claim is injectivity of the rank-3 reduced Burau representation of B_4; this claim is injectivity of Jones's Hecke/Temperley-Lieb algebra representation of B_4, which contains Burau as a summand and so follows from it
---

Jones's representation of `B_4` (V. F. R. Jones, *Hecke algebra representations of braid groups and
link polynomials*, Ann. of Math. 126 (1987); reference [14] of arXiv:2607.05283v1) is injective.

This is Corollary 1.1 of arXiv:2607.05283v1 (Bharathram–Birman–Brendle, unrefereed). There it
follows from the main theorem because "Jones introduced a representation of the braid group that
contains the (reduced) Burau representation as a summand ... As Jones points out, the faithfulness
of Burau representation ρ_n for any n implies the faithfulness of the Jones representation of the
braid group B_n" (quoted from the arXiv HTML render).

Route: `four-strand-jones-faithful-from-burau`, requiring
`four-strand-burau-representation-is-faithful`.

Scope note: the preprint makes no claim about the Jones polynomial or unknot detection.
Faithfulness of these braid representations does not by itself decide whether the Jones
polynomial detects the unknot.

## Attempts

- 2026-09-13 (lane z3-05-burau-theory): the implication from Burau faithfulness is written in the
  route. The claim stays open exactly as long as `four-strand-burau-representation-is-faithful`
  does.
