---
rg: 2
id: deepest-match-orientation-proof
kind: route
title: Read the eaten prefix through the palindrome decomposition
target: deepest-match-orientation
requires: []
artifacts:
  - GroupApproximation/Sofic/GreendlingerCascade.lean
---

## Complete argument

The head palindrome is `P = c₁ ++ t₁ ++ invRev c₁`, reduced.  The
head–tail free reduction cancels a suffix `M` of `P` against a prefix
of the tail word `V`, and the cancelled region is one contiguous block
(free reduction of a concatenation of two reduced words).  The regime
hypothesis `|c₁| < |M| ≤ |t₁| + |c₁|` (the block does not reach past
`t₁` — otherwise the head factor's whole relator dies against the tail
and `conjEval_block_ne_one`-style minimality applies) writes
`M = t₁.drop (|t₁| − μ) ++ invRev c₁` with `μ = |M| − |c₁| ≥ 1`.
Taking formal inverses, the eaten prefix of `V` is
`invRev M = c₁ ++ invRev (t₁.drop (|t₁| − μ))`: its first `|c₁|`
letters are conjugator letters, its last `μ` letters are relator
letters, and they appear in that order.  The landing chunk contains the
final eaten position, which lies in the relator segment since `μ ≥ 1`.
Chunk contiguity and ordering is `exists_chunk_decomposition`
(GreendlingerChunks:192).  ∎

Formalization note: this is a statement about lists, provable directly
from the decomposition equalities; it should land beside the
CascadeLanding assembly and be consumed by the (α)-case discharge.
