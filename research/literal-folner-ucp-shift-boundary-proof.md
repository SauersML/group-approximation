---
rg: 2
id: literal-folner-ucp-shift-boundary-proof
kind: route
title: Read the two endpoint projections of the compressed bilateral shift
target: literal-folner-ucp-models-have-sharp-norm-hs-separation
requires:
  - literal-fp-via-folner-rf-core
artifacts:
  - research/artifacts/literal-folner-sharp-boundary-2026-08-30.md
---

In the regular Hilbert-`C*_(max)(K)`-module representation used by the
factorization route,

```text
Lambda(u)e_j=e_(j+1).
```

Compression to `F=[-L,L]` therefore sends `u` to the truncated shift
`S=P_F Lambda(u)P_F`.  All its nonzero matrix entries are the coefficient
unit, so applying the single Arveson extension does nothing to this matrix:

```text
Phi_F(u)=S tensor I_Q,       Phi_F(u*)=S* tensor I_Q.
```

Writing `p_j` for the rank-one projection onto `e_j` gives the exact
finite-dimensional identities

```text
SS*=I_F-p_(-L),              S*S=I_F-p_L.
```

Since `Phi_F` is unital,

```text
Phi_F(uu*)-Phi_F(u)Phi_F(u*)=p_(-L) tensor I_Q,
Phi_F(u*u)-Phi_F(u*)Phi_F(u)=p_L tensor I_Q.
```

Each right-hand side is a projection of rank `|Q|` in dimension
`N|Q|`.  Its operator norm is one, its normalized Hilbert--Schmidt norm
is `sqrt(|Q|/(N|Q|))=N^(-1/2)`, and its normalized trace is `1/N`.
No estimate is lost: all three values are equalities.
