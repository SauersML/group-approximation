---
rg: 2
id: a4-triangle-hs-regular-core
kind: claim
title: Hilbert--Schmidt near A4 triangles with regular generator traces are regular off a vanishing-dimensional residual
artifacts:
  - research/artifacts/a4-hs-regularity-compiler-2026-08-19.md
distinct_from:
  a4-triangle-zero-traces-force-regular: that is the exact character-table theorem for an exact A4 representation; this first uses flexible finite-group HS stability to reach such a representation from one approximate triangle relation.
  atlas-shortest-a4-triangle-packet: that identifies the 30 concrete atlas pair-cubes; this is the dimension-independent local analytic compiler which applies to each of them.
---

Let `A_n,B_n in U(d_n)` satisfy

```text
A_n^3=1,
B_n^2=1,
||(B_n A_n)^3-1||_2 -> 0,
tr(A_n), tr(B_n) -> 0.
```

Then the pair flexibly exactifies to exact representations

```text
rho_n:A4->U(m_n),
```

with `m_n/d_n->1` and normalized-HS comparison error tending to zero, and
`rho_n` contains a summand

```text
s_n Reg(A4)
```

whose codimension is `o(d_n)`.

No mixed-word trace hypothesis is needed.  Gowers--Hatami exactification is
uniform on the fixed twelve A4 normal forms, so the exactified order-three and
order-two generators retain asymptotically zero normalized character.  Those
two character values alone force the four A4 irreducible multiplicities into
the regular ratios `1:1:1:3`, exactly as in
`a4-triangle-zero-traces-force-regular`.

This strengthening matters in the atlas application: regularity of the two
individual `A8` chart restrictions supplies the generator traces automatically,
whereas a mixed trace such as `tr(B_n A_n)` would require an additional
separating-word hypothesis not present in the bare atlas feasibility criterion.
