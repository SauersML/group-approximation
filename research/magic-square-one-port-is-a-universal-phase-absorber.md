---
rg: 2
id: magic-square-one-port-is-a-universal-phase-absorber
kind: claim
title: A one-port Magic Square absorbs every source involution in four dimensions
artifacts:
  - research/magic-arrangement-profile-absorption-proof.md
distinct_from:
  join-tree-overlap-gadgets-have-no-contextual-escape: that proves acyclic overlap incidence classicalizes; this proves the canonical cyclic repair is representation-theoretically inert when coupled through one port or commuting parity profiles.
  finite-k-commuting-face-universal-completion: that studies whether a finite Pauli packet can control a growing code through noncentral labels; this gives an exact obstruction for RHS twists and one-port attachments before any growing-code analysis.
  lcs-parity-gadgets-preserve-odd-dictator-affine-hull: that is a scalar affine-closure theorem; this constructs finite-dimensional operator extensions through a contextual cycle.
---

Let `L` be any binary involution presentation with a distinguished
involution `z`.  Adjoin nine new involutions `a_(ij)` in a `3 by 3`
Magic Square, impose commutation within every row and column, and impose

```text
product_j a_(ij)=1                         for i=1,2,3,
product_i a_(ij)=1                         for j=1,2,
product_i a_(i3)=z.                                      (MSA1)
```

The last equation also makes `z` commute with its three cell variables.
Call the resulting one-port presentation `MS_z(L)`.

Every operator representation `rho` of `L` extends to an operator
representation of `MS_z(L)` after tensoring by `C^4`.  Explicitly, with

```text
P_+=(1+rho(z))/2,       P_-=(1-rho(z))/2,                (MSA2)
```

put the all-identity scalar square on `P_+` and the standard two-qubit
Pauli Magic Square on `P_-`.  The last column product is then
`P_+-P_-=rho(z)`, while all other displayed products are one.

Consequently, for every representation class closed under finite tensor
amplification,

```text
L has a representation in the class
iff MS_z(L) has a representation in the class.                         (MSA3)
```

This applies in particular to finite-dimensional, matrix-tracial, and
commuting-operator perfect LCS models.  Any finite family of disjoint
one-port squares attached to arbitrary, even mutually noncommuting, source
involutions can be absorbed sequentially, at a dimension cost `4^k`.
Thus a Magic-Square cycle controlled through one source observable cannot
eliminate an odd long-code sector or create a finite-versus-commuting
separation.

There is a sharp extension to all finite magic arrangements in which every
new cell variable occurs in exactly two equation contexts.  Let `G` be the
connected context-intersection graph and let a scalar sign profile prescribe
the product at every vertex.

* If `G` is planar, the finite-dimensional realizable profiles are exactly
  the even-parity profiles, already realized by scalar edge signs.
* If `G` is nonplanar, every sign profile has a finite-dimensional operator
  realization.

The second bullet follows from Arkhipov's planarity theorem plus edge-sign
gauge transitivity; the first is its other direction.  Hence, when coupled
through mutually commuting central source ports, an arrangement gadget is
either one affine total-parity check or a finite-dimensional universal
absorber.  It never selects the singleton dictators from their odd affine
hull.

The remaining cyclic escape must therefore use at least two genuinely
noncommuting source ports in one connected gadget, with shared cells that
prevent sectorwise control, and must prove a dimension-independent reverse
decoder.  Merely twisting Magic-Square right-hand sides, attaching private
squares, or using any degree-two magic arrangement is closed.
