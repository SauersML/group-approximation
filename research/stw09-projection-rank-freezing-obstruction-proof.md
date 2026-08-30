---
rg: 2
id: stw09-projection-rank-freezing-obstruction-proof
kind: route
title: Use the norm-one gap between different projection ranks
target: stw09-full-matrix-coherence-rational-core-criterion
requires: []
artifacts:
  - research/artifacts/stw09-matrix-coherence-rank-obstruction-2026-08-30.md
---

Assume first that the coherent full-matrix system exists.  Put

```text
q_(j,n)=rho_n(z_j).
```

These are projections.  A unital embedding
`alpha_n:M_(k_n)->M_(k_(n+1))` is, up to a target unitary, an amplification;
in particular `k_(n+1)=m_n k_n` and it preserves normalized traces.

For each `j`, coherence gives

```text
||q_(j,n+1)-alpha_n(q_(j,n))|| < 1
```

eventually.  Two projections in one matrix algebra at distance strictly less
than `1` are unitarily equivalent and hence have the same rank.  Therefore

```text
tr_(k_(n+1))(q_(j,n+1))
 = tr_(k_(n+1))(alpha_n(q_(j,n)))
 = tr_(k_n)(q_(j,n))
```

eventually.  This sequence is eventually one rational number.  Its assumed
limit is `tau(z_j)`, proving that every central weight is rational.

Conversely suppose `tau(z_j)=c_j` is rational for all `j`.  Choose `k` large
enough that

```text
m_j = k c_j/d_j
```

is a positive integer for every `j`.  Since `sum_j c_j=1`,
`sum_j d_j m_j=k`.  The direct sum of `m_j` copies of the defining
representation of each `M_(d_j)` gives a unital homomorphism
`rho:E->M_k` satisfying `tr_k rho=tau` exactly.  Set

```text
k_n=2^n k,
rho_n=rho tensor 1_(2^n),
alpha_n(x)=x tensor 1_2.
```

Then both trace convergence and coherence are exact.  This proves the
equivalence.

For the ambient consequence, `E subset MD(psi_n)` makes `psi_n|E` a unital
star homomorphism.  Apply the necessity argument to these restrictions.
No multiplicativity of `psi_n` outside `E` is used.

The constant `1` is sharp for the rank argument: projections of different
ranks can have distance exactly `1`, but never less.  Thus neither tracial
`2`-norm closeness nor passage to a tracial quotient can replace the
operator-norm coherence used here.
