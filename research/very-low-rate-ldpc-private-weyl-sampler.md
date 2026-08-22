---
rg: 2
id: very-low-rate-ldpc-private-weyl-sampler
kind: claim
title: Build the private Weyl sampler from very-low-rate LDPC coordinate functionals
distinct_from:
  independent-private-labels-have-growing-dual-distance: that rules out local checks for independently selected labels; this redesigns the label distribution by starting from a sparse kernel.
  positive-rate-tanner-tests-have-contextual-models: that rules out positive-rate operator agreement; this has length Theta(r squared), dimension r, and adds a full exterior-square overlay.
---

OPEN.  Construct two binary bounded-row/column-weight parity-check systems
of length `K=Theta(r^2)` and nullity exactly `r` such that, after identifying
their coordinate functionals with

```text
a_t,b_t in F_2^r,
```

a pairing of the coordinates has the matrix-valued private Weyl energy gap
of `private-random-weyl-sampler-forces-growing-matrix-dimension`.

Add a degree-one disjoint commutation overlay satisfying
`disjoint-private-pairs-expand-the-full-exterior-square` separately on both
codes.  Prove that every near-perfect tracial reflection representation of
the resulting bounded-local system rounds on the same Hilbert space to its
scalar kernel PVM with a dimension-independent modulus.

The scalar and class-two counts are feasible: sparse checks define the
character code in linear size, nullity `r=Theta(sqrt K)` lies exactly at the
exterior-square threshold, and the degree-one overlay kills that entire
layer.  The unresolved tasks are (i) a sparse-kernel ensemble whose coordinate
functionals retain the Weyl metric-entropy gap, and (ii) exclusion/stability
of the genuinely nonnilpotent contextual quotient left after class two.

The sparse-inverse pseudorandomness problem is now bypassed by
`repeated-good-ldpc-coordinates-give-private-weyl-sampler`.  Start with an
ordinary constant-rate, constant-distance bounded-check code of length
`Theta(r)`, repeat its whole coordinate system `Theta(r)` times, and use
random perfect matchings of the repeated coordinates.  This supplies the
private matrix Weyl gap, linear-size bounded occurrence, recursive selection,
and a uniform full-exterior-square overlay.

Accordingly the sole remaining assertion in this node is the arbitrary-
operator one: prove that near-perfect local codeword PVMs, replicated
equality checks, and the exterior-square matching round on the same Hilbert
space to the scalar kernel.  The overlay eliminates every central class-two
escape, but existing results do not exclude a genuinely nonnilpotent
contextual quotient or provide a uniform HS correction for it.
