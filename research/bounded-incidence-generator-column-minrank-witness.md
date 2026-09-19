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

**ESTABLISHED.**  There are asymptotically good generator-column multisets
`(a_i)_(i<=K),(b_j)_(j<=K')`, with `K,K'=Theta(n)`, and bipartite edge sets
`E_n` of uniformly bounded degree such that the affine completion rank

```text
r(E_n)=min { rank(B):
  a_i^T B b_j=a_i.b_j for every (i,j) in E_n }
```

tends to infinity.  More importantly, below one fixed normalized-HS sampled-
test defect, exact additive X and Z laws force local dimension tending to
infinity on the same Hilbert space.

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

The discrete scalar-Weyl condenser is now established by
`private-random-generator-columns-form-affine-rank-condenser`.  A degree-one
matching of `64r^2` private random pairs in an active `r`-space stays at
relative distance at least `1/4` from every rank-at-most-`r/4` bilinear form;
embedding it in ambient dimension `N=r^2` gives scalar carrier dimension
`2^Omega(sqrt(N))` at a fixed sign-error threshold.  Appending a good base
generator block preserves uniform column spectral gaps and linear total
length.

The matrix-valued/HS promotion is now supplied by
`private-random-weyl-sampler-forces-growing-matrix-dimension`.  A metric-
entropy argument samples the full uniform Weyl energy simultaneously over
all exact additive representations of dimension at most `r`.  The full Weyl
gap then yields, for ambient `N=r^2`, one fixed sampled HS threshold forcing
`d>r=sqrt(N)`.  Thus arbitrary multiplicity and relative basis position do
not provide an escape.

What remains downstream is syntactic: choose a recursive/finite-presentation
realization of the existential random columns, and exactify approximate
additive laws at uniform word cost.  Those requirements belong to the Cayley
incidence/compiler nodes, not to this analytic dimension-witness claim.

There is no contradiction with the ordinary sparse-Pauli model.
`bounded-degree-partial-matrices-have-constant-completion-rank` proves that
an unrestricted degree-`Delta` partial binary matrix has completion rank
bounded only by `Delta`.  Its greedy row labels do not respect dependencies
among repeated generator columns.  Those additive dependencies are exactly
what forces the triangular block in the new exact witness.
