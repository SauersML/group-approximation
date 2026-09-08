---
rg: 2
id: finite-packet-collapse-via-fixed-algebra
kind: route
title: Apply fixed-algebra transport to the finite packet group algebra
target: finite-noncommutative-packet-compression-collapse
requires:
  - finite-dimensional-kazhdan-fixed-algebra-transport
artifacts:
  - research/artifacts/finite-block-perfect-mf-radicals.md
---

Given the finite subgroup F normalized by the Kazhdan group L, form the
finite-dimensional unital algebra A=C*(rho(F)) in the norm matrix corona.
It is normalized by rho(L). If f in F is fixed by tLt^-1, then rho(f)
belongs to A^(tLt^-1). The prerequisite identifies this algebra with A^L,
so rho(f) commutes with rho(L), exactly the target's conclusion.

This is a second proof of the finite packet result. The normalized
Hilbert--Schmidt vector argument is Theorem 1 in Section 2 of
`research/artifacts/finite-block-perfect-mf-radicals.md`.
It does not use the older weighted cocycle construction.
