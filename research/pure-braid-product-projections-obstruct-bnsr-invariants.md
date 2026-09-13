---
rg: 2
id: pure-braid-product-projections-obstruct-bnsr-invariants
kind: claim
title: "Zero-sum characters supported on disjoint strand blocks A_1..A_r miss Sigma^D(P_n) with D = sum(|A_i| - 2)"
distinct_from:
  pure-braid-top-bnsr-invariants-are-center-nonvanishing: that claim computes Sigma^m(P_n) exactly for m >= n-2; this gives characters outside the lower invariants, from several strand blocks at once.
artifacts:
  - research/artifacts/zp-pure-braid-bnsr-middle-range-2026-09-13.md
---

Let `A_1, ..., A_r <= {1, ..., n}` be pairwise disjoint with `|A_i| >= 3`, and
let `D = sum_i (|A_i| - 2)`. Let `chi = sum a_{ij} omega_{ij}` be a nonzero
character of `P_n` such that `a_{pq} = 0` unless `p, q` lie in a common block
`A_i`, and `sum_{p<q in A_i} a_{pq} = 0` for every `i`. Then
`[chi] notin Sigma^D(P_n)`.

For `r = 1` and `A = {1, ..., m}` this is the negative half of Zaremsky's
separation theorem (arXiv:1507.08597, Theorem 5.7), for every zero-sum
character on `m` strands rather than only `chi_n^m`. For `n = 6` and two
disjoint triples it gives characters in `Sigma^1(P_6)` (on no KMM circle)
outside `Sigma^2(P_6)`.

Status: UNREVIEWED (lane z1-09-pure-braid, 2026-09-13).
