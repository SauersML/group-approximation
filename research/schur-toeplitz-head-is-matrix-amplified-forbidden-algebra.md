---
rg: 2
id: schur-toeplitz-head-is-matrix-amplified-forbidden-algebra
kind: claim
title: Every packet-headed Toeplitz prefix is a matrix amplification of the forbidden Schur algebra
distinct_from:
  toeplitz-finite-head-centralizes-deep-tail: that identifies scalar matrix units in the bare Toeplitz ring; this carries the full forbidden packet ideal as the matrix coefficient algebra.
  schur-idempotent-is-an-injective-toeplitz-defect: that identifies one forbidden idempotent with the first defect; this computes all finite prefixes and their exact tail action.
  schur-toeplitz-envelope-has-proper-self-embedding: that constructs the recursive endomorphism; this gives its finite head/deep tail tensor interface.
---

Put `A_f=k[B_f]`, `A_f^-=P_fA_fP_f`, with unit `P_f`, and for `N>=1`
define

```text
F_N^-=span_k{x^i a y^j: 0<=i,j<N, a in A_f^-}.             (SHM1)
```

Then

```text
F_N^- isomorphic to M_N(A_f^-),                             (SHM2)
```

under `E_ij tensor a |->x^iay^j`. Moreover, for every `r in R_f`,

```text
sigma^N(r)=x^N r y^N+epsilon(r)sum_(i=0)^(N-1)e_i,
e_i=x^iP_fy^i,                                             (SHM3)
```

and hence

```text
c sigma^N(r)=sigma^N(r)c=epsilon(r)c
for every c in F_N^-.                                     (SHM4)
```

Thus the first `N` Toeplitz sites do not merely contain scalar head matrix
units. They contain the complete semisimple packet summand indexed by the
forbidden selector characters, while the deep tail acts as a scalar on it.
The orientation formerly represented by `P_f=2D(Z_C-Z_B)` is therefore an
honest coefficient-algebra factor of every finite head.

This is the exact tensor interface needed by the Heisenberg/Schur recurrence.
It does not assert that an arbitrary normalized-HS representation of
`EL_5(R_f)` is close to a coefficient-ring representation; that matrix-only
decoding remains the analytic content of
`hs-schur-toeplitz-root-defect-collapse`.
