---
rg: 2
id: barreto-minian-concatenable-minima-give-local-indicability
kind: claim
title: A deficiency-one homology circle presentation whose relators but one have concatenable minima defines a locally indicable group (Barreto--Minian)
distinct_from:
  lot-groups-are-torsion-free: that is the open statement for every LOT group; this is the general presentation criterion that proves local indicability, hence torsion-freeness, whenever its combinatorial hypothesis can be met.
  crossing-pair-two-cycle-lot-groups-are-locally-indicable: that is an infinite class of LOT groups obtained by meeting this criterion after one Tietze elimination; this is the criterion itself, for arbitrary presentations.
artifacts:
  - research/artifacts/hl-lot-torsion-2026-09-14.md
---

Imported through `barreto-minian-concatenable-minima-citation`.

**Definitions** (Barreto--Minian, Definitions 2.2 and 2.4). For a word `r` with
generators assigned weight `1`:

- the **multiset of minima** `m(r)` is the multiset of letters of `r` with exponent `-1`
  at which the sequence of total exponents of initial subwords attains its minimum `m`,
  together with the letters with exponent `+1` at which it attains `m + 1`;
- multisets `A_1, ..., A_n` are **concatenable** if some ordering `A_{i_1}, ..., A_{i_n}`
  has, for every `j`, an element of `A_{i_j}` of multiplicity `1` that is not in
  `A_{i_1} ∪ ... ∪ A_{i_{j-1}}`.

**Claim** (Barreto--Minian, Theorem 2.5). Let
`P = < a_1, ..., a_{k+2} | r_1, ..., r_k, s >` be a presentation of deficiency `1` of a
group `G` with `H_1(G) = Z` (for some `k >= 0`), in which all relators are cyclically
reduced and have total exponent `0`. If `m(r_1), ..., m(r_k)` are concatenable, then `G`
is locally indicable.

Equivalently, via the I-values of the source (their Remark on I-values): the letters of `r`
attaining the minimum I-value, where a positive letter carries the total exponent of the
preceding initial subword and a negative letter the total exponent after it.

**Standard consequence used downstream.** A locally indicable group is torsion-free: a
nontrivial finite cyclic subgroup admits no homomorphism onto `Z`.
