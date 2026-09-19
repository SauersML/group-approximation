---
rg: 2
id: literal-folner-ucp-shift-boundary-proof
kind: route
title: Read the two endpoint projections of the compressed bilateral shift
target: literal-folner-ucp-models-have-sharp-norm-hs-separation
requires:
  - literal-group-factorization-property
artifacts:
  - GroupApproximation/Analysis/QuasiRegularCompression.lean
  - GroupApproximation/Analysis/LocallyRFByIntAmenableTrace.lean
  - GroupApproximation/Analysis/LocallyRFByIntAction.lean
  - research/artifacts/literal-factorization-folner-ucp-2026-08-30.md
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

Use the concrete u.c.p. maps in the established proof
`literal-fp-via-folner-rf-core`.  They compress the honest quasi-regular
representation of `E` on `l2(E/J)` to the coordinates
`{0,...,N-1} x Q`.  For the stable-letter generator `u`, the exact action
formula gives

```text
Lambda(u)e_(j,q)=e_(j+1,q)
```

away from the last level.  Compression therefore sends `u` to the truncated
shift `S` tensored with the identity on the quotient label:

```text
Phi_F(u)=S tensor I_Q,       Phi_F(u*)=S* tensor I_Q.
```

Writing `p_j` for the rank-one projection onto level `j` gives the exact
finite-dimensional identities

```text
SS*=I_F-p_0,                 S*S=I_F-p_(N-1).
```

Since `Phi_F` is unital,

```text
Phi_F(uu*)-Phi_F(u)Phi_F(u*)=p_0 tensor I_Q,
Phi_F(u*u)-Phi_F(u*)Phi_F(u)=p_(N-1) tensor I_Q.
```

Each right-hand side is a projection of rank `|Q|` in dimension
`N|Q|`.  Its operator norm is one, its normalized Hilbert--Schmidt norm
is `sqrt(|Q|/(N|Q|))=N^(-1/2)`, and its normalized trace is `1/N`.
No estimate is lost: all three values are equalities.
