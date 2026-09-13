---
rg: 2
id: sl4z-representations-have-sl2-invariant-vectors
kind: claim
title: Every finite-dimensional unitary representation of SL_4(Z) has a block-SL_2(Z) fixed vector, so SL_4(Z) is not purely matricial field
---

ESTABLISHED (literature import).  Let `SL_2(Z) <= SL_4(Z)` be the upper-left
block `[[*,*,0,0],[*,*,0,0],[0,0,1,0],[0,0,0,1]]`.  Every finite-dimensional
unitary representation `rho` of `SL_4(Z)` has a nonzero `SL_2(Z)`-fixed vector.
Consequently, with `S, T` the standard generators of `SL_2(Z)`,
`||rho(S + S^(-1) + T + T^(-1))|| = 4` for every such `rho`, while
`||lambda_(SL_4(Z))(S + S^(-1) + T + T^(-1))|| < 4`, so no sequence of
finite-dimensional unitary representations of `SL_4(Z)` converges strongly to
the regular representation.

The same holds for every group containing `SL_4(Z)`, since strong convergence
passes to subgroups and the restriction of a finite-dimensional representation
is finite-dimensional.
