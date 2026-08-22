---
rg: 2
id: bounded-incidence-generator-column-minrank-witness
kind: claim
title: Build a robust bounded-incidence generator-column minimum-rank witness
distinct_from:
  sparse-generator-column-sampling-has-bilinear-kernel: that proves full-table spectral recovery is impossible and defines the exact affine completion rank; this asks whether that rank can nevertheless grow and be robust in normalized Hilbert--Schmidt norm.
  pauli-braiding-test-exponential-dimension: that supplies a robust dimension witness with a dense logical cross distribution; this asks for bounded logical incidence suitable for separated Cayley placement.
  expander-cloud-reduction-preserves-pauli-dimension-gap: that replaces repeated occurrences but retains all dense logical tests; this sparsifies the logical cross tests themselves.
---

OPEN.  Construct asymptotically good generator-column multisets
`(a_i)_(i<=K),(b_j)_(j<=K')`, with `K,K'=Theta(n)`, and bipartite edge sets
`E_n` of uniformly bounded degree such that the affine completion rank

```text
r(E_n)=min { rank(B):
  a_i^T B b_j=a_i.b_j for every (i,j) in E_n }
```

tends to infinity.  More importantly, prove a dimension-independent robust
version: below one fixed normalized-HS sampled-test defect, exact additive X
and Z laws (or their uniformly correctable versions) force local dimension at
least `2^r_n` for some `r_n->infinity`, on the same Hilbert space.

Ordinary spectral expansion and high girth do not imply this.
`sparse-generator-column-sampling-has-bilinear-kernel` gives, for every
`|E_n|<n^2`, an exact bilinear twist with zero sampled defect and constant
full-table defect.  A positive proof must therefore be a direct rank-metric
local-test theorem for the affine syndrome `T_E(I)`, not a derandomized
comparison with the complete product measure.

If established together with sign-separated Cayley placement, this replaces
the complete logical Pauli rectangles by a sparse robust dimension witness
without an expander-cloud sheet loss.

The exact half is now solved by
`degree-one-generator-columns-have-sqrt-minrank-but-no-gap`: private repeated
basis columns force a triangular identity block and give
`r(E)=Theta(sqrt(n))` even when the sampled occurrence graph is a matching.
The same construction has no fixed robust gap: its diagonal constraints have
vanishing density, and even after diagonal reweighting a `k`-block completion
has rank `k` and error `1/k+o(1)`.  Thus the remaining content of this OPEN
node is precisely a constant-distance affine rank condenser: the ideal
syndrome must stay a fixed relative Hamming distance from every bounded-rank
completion, followed by its amplification-stable HS promotion.

There is no contradiction with the ordinary sparse-Pauli model.
`bounded-degree-partial-matrices-have-constant-completion-rank` proves that
an unrestricted degree-`Delta` partial binary matrix has completion rank
bounded only by `Delta`.  Its greedy row labels do not respect dependencies
among repeated generator columns.  Those additive dependencies are exactly
what forces the triangular block in the new exact witness.
