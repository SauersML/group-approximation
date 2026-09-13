---
rg: 2
id: ollivier-wise-kazhdan-rips-construction
kind: claim
title: Every countable group is a quotient of a torsion-free two-dimensional graphical small cancellation group by a Kazhdan normal subgroup (Ollivier--Wise)
distinct_from:
  hyperbolic-kazhdan-cover-of-leavitt-unit-group: that uses the Belegradek--Osin Rips construction over a lattice in Sp(2,1), which controls torsion and hyperbolicity but not dimension; this is the graphical-small-cancellation Rips construction, whose total group has dimension two.
---

**ESTABLISHED (literature import).** For every countable group `Q` there is a short exact sequence
`1 -> N -> G -> Q -> 1` in which:
- `G` is torsion-free and has a graphical `1/6` small cancellation presentation;
- `N` has property (T);
- `G` is finitely presented when `Q` is.

A graphical `Gr'(1/6)` presentation makes `G` torsion-free and of dimension two, so
`cd G <= 2`. When the presentation is finite it also makes `G` word-hyperbolic.

Source: Y. Ollivier and D. T. Wise, *Kazhdan groups with infinite outer automorphism group*,
arXiv:math/0409203v1. Theorem 1.1 and Section 2.1 were read from the PDF on 2026-09-13. The
verbatim text is in `ollivier-wise-kazhdan-rips-construction-citation`.

Consumer: `cd-two-group-with-infranormal-kazhdan-pair`.
