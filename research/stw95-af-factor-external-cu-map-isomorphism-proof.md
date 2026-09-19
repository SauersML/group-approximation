---
rg: 2
id: stw95-af-factor-external-cu-map-isomorphism-proof
kind: route
title: Prove the external Cu isomorphism at finite stages and pass to the AF limit
target: stw95-af-factor-external-cu-map-isomorphism
requires: []
---

For a matrix algebra `M_r`, Morita invariance identifies both
`Cu(M_r) tensor_Cu Cu(B)` and `Cu(M_r tensor B)` with `Cu(B)`, compatibly with
the external product.  Tensor products in `Cu` distribute over finite direct
sums, so the same holds for every finite-dimensional algebra `F`.

Write `C=lim F_i` as a directed limit of finite-dimensional algebras.  Minimal
tensoring by `B` commutes with this inductive limit.  Continuity of
the Cuntz semigroup and separate preservation of inductive limits by the Cu
tensor product, as developed by Antoine--Perera--Thiel, identify both sides
with the inductive limits of the finite-stage terms.  The compatible
finite-stage external-product isomorphisms therefore induce the claimed
isomorphism.

This is also exactly Antoine--Perera--Thiel, arXiv:1410.0483, Proposition
6.4.13 (the AF factor is nuclear, so maximal and minimal tensor products
coincide).
