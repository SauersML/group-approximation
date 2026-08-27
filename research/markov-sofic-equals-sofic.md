---
rg: 2
id: markov-sofic-equals-sofic
kind: claim
title: Frobenius approximate group models in doubly stochastic matrices are exactly sofic models
artifacts:
  - research/artifacts/hyperlinear-extreme-breakthroughs-2026-08-18.md
---

Call a finite table **Markov-sofic** when, on one finite state space, it admits
doubly stochastic matrices `P_g` with normalized-Frobenius multiplication
defect tending to zero, `P_e` tending to `I`, and normalized traces tending to
zero on the nonidentity elements being separated.

**Theorem.** A group is Markov-sofic if and only if it is sofic.

The nontrivial direction is dimension-free. Tested inverse relations make
`P_g P_{g^{-1}}` close to `I`; `birkhoff-approx-inverse-permutation` then
rounds every `P_g` to a permutation with Frobenius error `o(1)`. Because every
doubly stochastic matrix has operator norm at most one, multiplication errors
survive this rounding, and for permutations
`||S-T||_{2,N}^2 = 2 d_H(S,T)`. Trace/fixed-point separation survives by
Cauchy--Schwarz. The converse is immediate because permutation matrices are
doubly stochastic.

This identifies the genuine positive Q3.4 gate: not final Birkhoff rounding,
but **phase/interference removal while preserving multiplication, inverses and
regular trace data**.
