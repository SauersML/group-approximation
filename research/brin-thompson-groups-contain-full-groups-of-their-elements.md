---
rg: 2
id: brin-thompson-groups-contain-full-groups-of-their-elements
kind: claim
title: For g in nV and a clopen g-invariant set U, the whole topological full group of g on U (extended by the identity) lies in nV
distinct_from:
  brin-thompson-first-return-maps-lie-in-kv: that puts one first-return map of a kV element into kV; this puts every piecewise-power map of g on clopen pieces into nV, which contains all first-return maps with bounded return time.
  full-shift-topological-full-group-embeds-in-2v: that is one conjugacy for the full shift; this is the closure property of nV under clopen gluing that makes any element's full group a subgroup.
---

**ESTABLISHED** (lane proof below, elementary; not independently reviewed; no novelty claimed).

## Statement

Let `C = {0,1}^N` and let `nV` act on `C^n` as in Brin's definition: an element is a
homeomorphism given by two partitions of `C^n` into finitely many dyadic boxes and a bijection
between them, acting on each box by the prefix replacement
`(p_1 w_1, ..., p_n w_n) -> (q_1 w_1, ..., q_n w_n)`.

Let `g ∈ nV`, and let `U ⊆ C^n` be clopen with `g(U) = U`. Let `h` be a homeomorphism of `C^n`
that is the identity off `U` and satisfies `h(y) = g^(m(y))(y)` on `U` for a continuous
`m : U -> Z`. Then `h ∈ nV`. So `[[g|_U]]`, extended by the identity, is a subgroup of `nV`.

## Proof

- `m` takes finitely many values, on clopen sets `U_1, ..., U_r`. Every clopen subset of `C^n` is a
  finite union of dyadic boxes, and the intersection of two dyadic boxes is a dyadic box or empty.
- For each `j`, fix a box representation of `g^(m_j) ∈ nV`. Intersect its domain boxes with a box
  decomposition of `U_j`. On each resulting box `B`, `h = g^(m_j)` acts by the restriction of a
  prefix replacement to a sub-box, which is again a prefix replacement onto a dyadic box.
- Together with the boxes of `C^n \ U`, where `h` is the identity, this is a finite box partition on
  which `h` acts by prefix replacements. Their images are pairwise disjoint and cover `C^n` because
  `h` is a bijection, so `h` is an element of `nV`.
