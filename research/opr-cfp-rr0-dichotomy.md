---
rg: 2
id: opr-cfp-rr0-dichotomy
kind: claim
title: Simple real rank zero algebras with the corona factorization property are stably finite or purely infinite (Ortega-Perera-Rordam, Zhang)
distinct_from:
  stw29-projection-qq-characterizes-rr0-dichotomy: that proves the dichotomy is equivalent to projection-level QQ on V(A) and that almost unperforation suffices; this imports the literature theorem that the corona factorization property of A suffices, via the monoid CFP of V(A).
---

**Theorem (Ortega--Perera--Rordam, arXiv:0904.0541, Corollary 5.16;
proved earlier in an unpublished paper of S. Zhang).**  A separable simple
C\*-algebra of real rank zero with the Corona Factorization Property is either
stably finite or purely infinite.

Separability can be dropped by passing to a suitable separable
sub-C\*-algebra (remark preceding Corollary 5.16 in the same paper).

The mechanism has two parts, both proved in the same paper.

1. For `A` of real rank zero with `A tensor K` having a countable approximate
   unit of projections, `A` has the CFP (every full projection of
   `M(A tensor K)` is properly infinite) iff the monoid `V(A)` has the monoid
   CFP (Theorem 5.8(ii)): for every full increasing sequence `(x_n)`, every
   sequence `(y_n)` and every `m`, if `x_n <= m y_n` for all `n` then
   `x_1 <= y_1 + ... + y_k` for some `k` (Definition 5.4).
2. In a conical refinement monoid with the CFP, an order unit `u` such that
   `m u` is properly infinite is itself properly infinite (Theorem 5.14(ii)).
   The proof splits `u` into an infinite sequence of order units
   `t_1 + ... + t_k <= u` with every `m t_i` properly infinite
   (`opr-properly-infinite-multiple-splits`), then applies the CFP twice to
   obtain `2u <= t_1 + ... + t_l <= u`.

For a simple real-rank-zero algebra this is projection-level `(QQ_V)`, so the
dichotomy follows exactly as in `stw29-projection-qq-characterizes-rr0-dichotomy`.
Sufficient conditions for the CFP in this class include almost unperforated
`V(A)`, or `n`-comparison for some `n` (Corollary 5.9).
