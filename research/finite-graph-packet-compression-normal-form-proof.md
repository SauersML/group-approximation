---
rg: 2
id: finite-graph-packet-compression-normal-form-proof
kind: route
title: Separate the vertex algebra from the stable-letter double coset
target: finite-graph-packet-compression-wandering-no-go
requires:
  - one-round-v4-lamps-wordize-a-bcs-losing-projection
  - uniform-clock-reflection-block-encodes-game-hamiltonian
---

Because `q` has support in `K`, every group basis element occurring in
`qwq` lies in `KwK`.  If one such element lay in `K`, then
`k_1 w k_2 in K` for some `k_1,k_2 in K`, which would imply `w in K`.
Thus `(FGP2)` holds whenever `w notin K`.  The group elements form an
orthonormal basis of `L^2(L(G))`; `V` is supported in `K`, so Pythagoras
gives `(FGP3)`.  If `w in K`, finiteness of `K` makes its powers periodic.

Fundamental groups of finite graphs of finite groups are virtually free and
residually finite.  Residual finiteness supplies finite quotients injective
on all pairwise differences in the finite support of `q(w-V)q`.  Expanding
the squared Hilbert--Schmidt norm in the quotient regular character then
reproduces its group regular `L^2` norm exactly.  These exact finite models
rule out even a qualitative version of `(FCW1)`.

For the proposed conjugate product, Britton normal form says that
`t a t^(-1)` loses its stable letters precisely when `a` belongs to the
associated edge subgroup, in which case the defining HNN relation replaces
it by the corresponding vertex element.  If every factor loses its stable
letters, the whole product lies in a finite vertex packet; if some factor
does not, the reduced word lies outside that packet and the double-coset
floor applies.  The finite V4 wordization and clock reflection make `V`
nonzero in the selected packet corner, which is exactly the hypothesis
needed in `(FGP1)`.
