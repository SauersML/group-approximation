---
rg: 2
id: pairwise-coevaluation-retention-commutant-density-proof
kind: route
title: Count invariant endomorphisms and exclude compact factor intertwiners
target: pairwise-coevaluation-retention-has-commutant-density-decay
requires: []
---

Use the unitary identification

```text
H tensor conjugate(H) ~= S_2(H),
xi tensor conjugate(eta) |-> |xi><eta|.
```

The diagonal action becomes conjugation by `pi(g)`, so its fixed subspace is
`End_G(H)` and has dimension `c`.  Tensoring `n` such fixed spaces beside the
unpaired `H` gives dimension `d c^n` inside total dimension `d^(2n+1)`,
proving `(PCR1)`.  Schur decomposition gives
`End_G(H)=direct_sum_alpha M_(m_alpha)`, proving the multiplicity formula and
`(PCR2)`.  The elementary inequality `(1-x)^n<=exp(-nx)` yields the necessity
of `(PCR3)` for nonvanishing weights.

On `L^2(M)`, the same tensor--Hilbert--Schmidt identification proves the
first equality in `(PCR4)`.  If `0!=T in M' intersection S_2`, then
`T*T` is nonzero compact and belongs to `M'`.  A spectral projection above a
positive threshold is a nonzero finite-rank projection in `M'`; its range is
an invariant finite-dimensional subspace for the normal left action of
`M`.  The corresponding normal star homomorphism from the factor `M` to a
matrix algebra has zero kernel or total kernel.  It is nonzero, hence would
be injective, contradicting infinite dimensionality.  Therefore the
intersection is zero.
