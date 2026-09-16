---
rg: 2
id: small-spectral-radius-integer-matrices-classified
kind: claim
title: Every indecomposable integer symmetric matrix of spectral radius below 2.019 is cyclotomic or equivalent to one of seventeen signed graphs on at most eighteen vertices, with ten possible radii
distinct_from:
  cyclotomic-integer-matrices-classified: that classifies spectral radius at most two, where infinite tessellation families occur; this is the next layer, radius in (2, 2.019), where only seventeen finite graphs occur
  integral-operator-norm-below-two-is-quantized: that is a group-ring statement below two proved through Pólya's theorem; this is a classification of finite integer matrices just above two, with no group in it
artifacts:
  - research/artifacts/determinant-norm-room-2026-09-16.md
---

**ESTABLISHED (literature import)** by
`small-spectral-radius-integer-matrices-classified-citation`.

J. McKee and C. Smyth, *Integer symmetric matrices of small spectral radius and
small Mahler measure*, arXiv:0907.0371 (July 2009, by identifier). The TeX
source was read on 2026-09-16 (Sections 1, 2 and 7).

**Conventions.**
- An *integer symmetric matrix* may have any integer entries, including on the
  diagonal.
- It is *indecomposable* if the graph of its nonzero off-diagonal entries is
  connected.
- It is *cyclotomic* if its spectral radius is at most `2`.
- *Equivalence* is `B = +-P^T A P` with `P in O_d(Z)`, a signed permutation. It
  preserves size and spectral radius.

> **Theorem** (label `T:spectral radius`). Up to equivalence, the
> indecomposable integer symmetric matrices having spectral radius less than
> 2.019 are either cyclotomic or have spectral radius equal to one of the ten
> values given in Table 1. The matrices having each such spectral radius are
> also given in this table.

**Table 1.** Radii and graphs, where the label is the number of vertices:

| # | radius | graphs |
| --- | --- | --- |
| 1 | 2.00659 | `10f = T_(1,2,6)` |
| 2 | 2.00960 | `10e` |
| 3 | 2.01076 | `11c = T_(1,2,7)` |
| 4 | 2.01348 | `10d`, `12b = T_(1,2,8)` |
| 5 | 2.01532 | `9d = T_(1,3,4)`, `10g`, `11a`, `11b`, `13a = T_(1,2,9)` |
| 6 | 2.01658 | `10h`, `14a = T_(1,2,10)` |
| 7 | 2.01746 | `15a = T_(1,2,11)` |
| 8 | 2.01809 | `16a = T_(1,2,12)` |
| 9 | 2.01854 | `17a = T_(1,2,13)` |
| 10 | 2.01887 | `12a`, `18a = T_(1,2,14)` |

**Consequence used downstream.** Every indecomposable noncyclotomic integer
symmetric matrix of spectral radius below `2.019` has at most `18` rows. So an
indecomposable integer symmetric matrix with at least `19` rows and spectral
radius below `2.019` has spectral radius at most `2`.

**Proof method (as described in Section 7).** Every noncyclotomic example
contains a minimal noncyclotomic one, by interlacing. The table is produced by
growing from the minimal ones, adding one vertex of charge `-1`, `0` or `1` at a
time, with degree at most `4`. The authors remark that all graphs found are
signed graphs with no charges. The growing is a computer search, and it was
not re-run here.

The bound `2.019` sits just below `2.019800887...`, the limit of the radii of
`T_(1,2,n)`. Above that limit there are infinitely many examples.
