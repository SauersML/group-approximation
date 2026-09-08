---
rg: 2
id: strict-coefficient-stabilizer-extraction-proof
kind: route
title: Tensor strict involution expectations and combine countable projection witnesses
target: commutation-stabilizers-are-relatively-embeddable
requires: []
artifacts:
  - research/artifacts/commutation-stabilizer-relative-embedding-2026-09-07.md
---

Lift the involution exactly to `S_n` and average onto its finite matrix
commutant. The squared expectation norm at an actor word converges to
`q_g=1-||[s,u_g]||_2^2/4`. On `k` tensor factors it is `q_(g,n)^k`.
A diagonal choice with coordinate errors at most `k^-3` preserves
canonical actor trace and multiplication, fixes words in the actual
commutation subgroup, and kills every fixed outside word because its
limiting coefficient is strictly below one. Extend the expectation
identity by 2-norm density to get the full scalar commuting square.

For a countable family, take the block involution `(2p_i-1)_i` in a
weighted direct sum with all weights positive. Its stabilizer is
exactly the intersection. The weighted sum remains CE and preserves
the canonical actor trace. Sections 1--2 of the artifact give the full
lift, diagonal, tensor, and countable-family arguments.
