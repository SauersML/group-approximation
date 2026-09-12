---
rg: 2
id: cofinite-lamp-subgroups-contain-center-proof
kind: route
title: Two lamp vectors with odd form value in a cofinite subspace commute up to eps
target: clifford-cover-cofinite-lamp-subgroups-contain-the-center
requires: []
artifacts:
  - research/artifacts/clifford-cover-phase-barrier-2026-09-12.md
---

Complete direct proof, artifact Section 2.
- **The lemma.** Take `u, u'` in `L_H` with `b_S(u, u') = 1`, and lifts in `H cap Vtilde_S`. Their commutator is
  `eps^(b_S(u,u')) = eps`, since lifts differ by central elements.
- **Complete graph.** By pigeonhole, three distinct sites `a, b, c` lie in one coset of `L_H`. Then
  `b_S(e_a + e_b, e_a + e_c) = b(a,c) + b(b,a) + b(b,c) = 1`.
- **Induced matching `{a_i, b_i}`.** By pigeonhole, distinct `i, j, k` have `e_(a_i) = e_(a_j)` and
  `e_(b_i) = e_(b_k)` modulo `L_H`. Then `b_S(e_(a_i) + e_(a_j), e_(b_i) + e_(b_k)) = 1`, because only the pair
  `{a_i, b_i}` is adjacent.
