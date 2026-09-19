---
rg: 2
id: noetherian-invariant-compression-rigidity
kind: claim
title: Chain-condition invariants are blind to one-sided compression
distinct_from:
  invariant-size-collapse: That claim's size distinguishes proper inclusions, so it collapses the compression itself to an equality of subgroups; this one assumes only a chain condition and no faithfulness, and concludes nothing about the subgroups — only that the invariant takes the same value on both, a blindness theorem in the FiniteQuotientBlindness pattern.
---

Let a group `H` act on a poset `P` by order-automorphisms, let `S` be a
conjugation-closed family of subgroups of `H`, and let `I : S -> P` be
**equivariant**: `I(h L h^{-1}) = h . I(L)`.  Suppose either

- `I` is monotone (`L_1 <= L_2` implies `I(L_1) <= I(L_2)`) and `P` has no
  infinite strictly descending chain, or
- `I` is antitone and `P` has no infinite strictly ascending chain.

Then `s L s^{-1} <= L` forces `s . I(L) = I(L)`; consequently
`I(s^k L s^{-k}) = I(L)` for every `k >= 0`.

**Slogan: Noetherian invariants cannot detect strict one-sided
compression.**  The totally-ordered faithful special cases are the proved
collapses: cardinality, `finrank`, `Nat.card`, Haar measure, commutant
dimension (`invariant-size-collapse`, `commutant-no-growth`).  The content
of dropping faithfulness is that the conclusion weakens from "the
compression is an equality" to "the invariant cannot see it" — exactly the
form needed by the envelope and fixed-tensor corollaries
(`zariski-envelope-compression-rigidity`,
`invariant-tensor-compression-rigidity`), where the compression is
genuinely proper.  Calibration for use as a no-go: any proposed
finite-dimensional detector of a strict compression must fail one of the
three hypotheses — equivariance, monotonicity, or the chain condition.
