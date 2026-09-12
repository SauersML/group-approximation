---
rg: 2
id: regular-p3-gauge-surplus-proof
kind: route
title: Decompose the regular parahoric representation through its Clifford corner
target: regular-p3-parahoric-bands-have-twisted-gauge-surplus
requires:
  - p3-full-parahoric-interlock-enforces-inverse-mackey-cocycle
---

Restrict `Reg(P)` to `N`; it is `|P/N|` copies of `Reg(N)`, hence the
`pi`-isotypic component has dimension `|P/N|(dim pi)^2`.  Clifford
factorization writes it as `H_pi` tensored with an inverse-projective
multiplicity module.  Comparing the regular character in the twisted group
algebra, or decomposing into projective irreducibles with regular
multiplicities, identifies that module as `(dim pi)` copies of the inverse
twisted regular representation.  Restriction of `Reg(G_a)` to `P_a` and
direct sums over depth preserve the formula blockwise.
