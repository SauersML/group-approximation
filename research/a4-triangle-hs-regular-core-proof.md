---
rg: 2
id: a4-triangle-hs-regular-core-proof
kind: route
title: Flexible finite-group stability plus the A4 character table
 target: a4-triangle-hs-regular-core
requires:
  - a4-triangle-zero-traces-force-regular
artifacts:
  - research/artifacts/a4-hs-regularity-compiler-2026-08-19.md
---

Choose fixed normal-form words `w_g(a,b)` for the twelve elements of
`A4=<a,b | a^3=b^2=(ba)^3=1>`.  Every one of the finitely many multiplication
identities `w_g w_h=w_(gh)` has a fixed derivation from the three presentation
relators.  Since the first two relators hold exactly, telescoping shows that
`g |-> w_g(A_n,B_n)` is an approximate representation of the finite group A4
with maximum normalized-HS multiplication defect tending to zero.

Gowers--Hatami's dimension-independent finite-group Hilbert--Schmidt stability
theorem (arXiv:1510.04085, Section 6) flexibly exactifies these maps to exact
representations `rho_n:A4->U(m_n)` with `m_n/d_n->1` and comparison error
`o(1)` on every group element.  Hence their normalized characters on the named
order-three and order-two elements tend to zero.

Write the four irreducible multiplicities as `m0,m1,m2,m3`, with dimensions
`1,1,1,3`.  The order-three character equation

```text
m0+omega*m1+omega^2*m2=o(m_n)
```

forces `m0=m1=m2+o(m_n)` pairwise, and the order-two equation

```text
m0+m1+m2-m3=o(m_n)
```

forces `m3=3m0+o(m_n)`.  Taking the componentwise minimum of
`m0,m1,m2,floor(m3/3)` extracts `s_n Reg(A4)` with `o(d_n)`-dimensional
complement.  This is exactly the claimed regular core.
