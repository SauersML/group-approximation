---
rg: 2
id: higman-theorem-three-reduces-to-enumerated-range
kind: claim
title: Higman's Section 2 reduces to one closure property -- that the range of a total computable enumeration is generated -- and his Lemma 2.8 as printed is false at the empty set
distinct_from:
  torsion-free-higman-embedding: that is the embedding theorem for recursively presented groups, the output of Higman's paper; this is one of the four inputs that theorem is currently assembled from, and it is about the sequence-space combinatorics of his Section 2.
artifacts:
  - GroupApproximation/Higman/TheoremThreeAssembly.lean
  - GroupApproximation/Higman/GeneratedEnumeration.lean
  - GroupApproximation/Higman/GeneratedBasic.lean
---

Higman's Theorem 3 --- every recursively enumerable subset of the sequence
space is built from `Z` and `S` by his nine operations --- was carried as one
input, `HigmanTheoremThree`.  It is now derived from the single closure
property

```text
EnumeratedRangeGenerated:
  for every total computable c : N -> List (Z x Z),
    { g : exists r, seqOfList (c r) = g }  is HigmanGenerated.
```

by `higmanTheoremThree_of_enumeratedRange`, and the four-input assembly is
restated as `statement_of_four_enumerated`.

Everything else Theorem 3 asked for is proved: finite unions
(`higmanGenerated_of_finite`), the empty set (`higmanGenerated_empty`), and
Higman's Lemma 2.8 (`exists_computable_enumeration`), which turns every
nonempty recursively enumerable set into exactly such a range.  What is left is
only the passage from finite unions to unions indexed by a total computable
enumeration.

## The source correction

Higman's Lemma 2.8 as printed (1961, p. 463) carries **no hypothesis on `X`**.
It is false at `X = empty`: there is no total function enumerating an empty
range.  The formalization restores `B.Nonempty`, and the empty case is handled
separately by `higmanGenerated_empty`.  This is a small correction and it is
load-bearing: without it the reduction above would be unsound at one point, and
the missing case is exactly the one a reader skips.

## Honest accounting of the gain

The converse is not formalized.  `EnumeratedRangeGenerated -> HigmanTheoremThree`
is proved; nothing proves the other direction, so the new input is not
*certified* weaker --- only narrower in what it quantifies over.  The header
notes that the converse (such a range is recursively enumerable) is the easy
direction of Theorem 3 and is simply not used, which means the two are
mathematically equivalent and the gain is one of shape rather than of strength.
Record it that way: the input count is unchanged at four, and the second input
is now a single closure property instead of the whole of Section 2.
