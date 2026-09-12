---
rg: 2
id: sl3-half-is-hyperfinite-hs-stable
kind: claim
title: SL3 over the dyadic localization is hyperfinitely Hilbert--Schmidt stable
distinct_from:
  character-rigidity-equals-hyperfinite-hs-stability: that imports the higher-rank lattice equivalence and the general character criterion; this records its concrete application to the S-arithmetic group SL3(Z[1/2]) using Peterson--Thom's localization character rigidity.
  sl3z-regular-microstates-are-congruence-correctable: that asks for correction in the nonamenable regular sector of SL3(Z); this corrects only amenable-limit microstates of the larger dyadic group.
---

The finitely generated group

```text
A=SL_3(Z[1/2])
```

is flexibly normalized-Hilbert--Schmidt stable on every sequence whose
limiting GNS von Neumann algebra is amenable (hyperfinitely
Hilbert--Schmidt stable).

Peterson--Thom, *Character rigidity for special linear groups*,
arXiv:1303.4007, treat `SL_n(R)` when `R` is a localization of an order in
a number field; their character classification applies to this `A`.
Every extremal character is finite-dimensional/finite-quotient or regular.
The regular character is not von Neumann amenable because `A` is
nonamenable.  Hence every von Neumann amenable character is a barycenter of
finite-dimensional characters, and finite barycenters are normalized
traces of finite direct sums.  Approximation of the barycenter by finite
ones shows that every amenable character is a pointwise limit of
finite-dimensional normalized traces.

Dogon--Vigdorovich's general character criterion for hyperfinite
Hilbert--Schmidt stability (the criterion imported with
`character-rigidity-equals-hyperfinite-hs-stability`) now gives the stated
flexible correction theorem.  No assertion is made about regular-character
microstates, whose GNS algebra is the nonamenable factor `L(A)`.
