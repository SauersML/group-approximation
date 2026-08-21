---
rg: 2
id: isotypic-finite-edge-forces-full-commuting-selector-support
kind: claim
title: A saturated finite edge type contains every compatible commuting-selector character
distinct_from:
  finite-selector-gadget-induction-barrier: that says every selector character occurs somewhere in the ambient finite group; this proves that every compatible character occurs inside the one selected target type whenever an HNN edge has full source-Gram saturation.
  common-source-hnn-bridges-need-one-gram-saturation-identity: that isolates source-Gram saturation as the missing scalar estimate; this gives a sharp no-go for obtaining that saturation from a logical-invariant finite edge type.
  gauge-doubling-gives-selector-flip-symmetries: that makes the logical products invariant under the gauge action; this proves that such invariance puts gauge doubling exactly inside the no-go hypothesis.
---

Let `H<=G` be finite, let `sigma` be an irreducible representation of `H`,
and let `A<=C_G(H)` be finite abelian.  Every element of `A intersect H` is
central in `H`, so Schur's lemma gives a character

```text
chi_0:A intersect H -> T
```

through which it acts in `sigma`.  Suppose one irreducible representation
`rho` of `G` contains **all** the `H`-type `sigma`, equivalently

```text
Ind_H^G(sigma) is rho-isotypic.                           (IFS1)
```

Then every character `chi` of `A` extending `chi_0` occurs in the joint
`A`-spectrum of `rho`.  In particular, if `A intersect H` is trivial, the
selected target type `rho` contains the full character cube `dual(A)`.

## Proof

Put `L=HA`.  Since `A` centralizes `H`, every extension `chi` of `chi_0`
defines an irreducible representation of `L` by

```text
(sigma tensor chi)(ha)=sigma(h)chi(a).                  (IFS2)
```

The compatibility on `A intersect H` makes `(IFS2)` well defined.  The
elementary Fourier decomposition of the finite abelian quotient gives

```text
Ind_H^L(sigma)
  = directSum_(chi extending chi_0) sigma tensor chi.    (IFS3)
```

Realize induced representations as equivariant functions on `G`.  The
functions supported on `L` form an `L`-invariant copy of
`Ind_H^L(sigma)` inside

```text
Res_L^G Ind_H^G(sigma).                                 (IFS4)
```

By `(IFS1)`, the right side of `(IFS4)` is a finite direct sum of copies of
`Res_L^G(rho)`.  Every summand in `(IFS3)` must therefore occur in
`Res_L^G(rho)`.  Restricting further to `A` proves that every compatible
`chi` occurs in `rho`.

## Source-Gram interpretation

Let `e_sigma in C[H]` and `p_rho in Z(C[G])` be the corresponding central
idempotents.  In the regular representation of `G`,

```text
(1-p_rho)e_sigma=0                                     (IFS5)
```

if and only if `(IFS1)` holds.  Indeed the irreducible summands of
`Ind_H^G(sigma)` are exactly the irreducible `G`-types on which
`e_sigma` is nonzero.  Thus an ordinary finite HNN edge whose selected
compression has full source Gram on the regular stationary packet,

```text
tau(e_sigma)-tau(e_sigma U^*p_rho Ue_sigma)=0,          (IFS6)
```

must satisfy `(IFS1)`.  If its logical selector subgroup centralizes the
edge type, the selected target type consequently has full selector support.
It cannot encode a proper nonlinear allowed set.

## Gauge-doubling audit

Gauge doubling does not evade the theorem.  Its incidence gauge flips both
shares and fixes every logical product `X=A B`.  Hence the subgroup generated
by the logical products centralizes the finite gauge edge.  If the edge type
were saturated into one selected context type, the theorem would put every
compatible logical selector character in that type, including every
forbidden nonlinear assignment.  Covariantization solves exact completeness,
but it cannot turn a logical-invariant finite edge into the common selected
source required by the Fanizza decoder.

## Consequence for the common-source cell

The tempting finite construction

```text
one common finite edge type sigma
  -> four HNN bridges
  -> four selected context types rho_c
```

cannot satisfy zero-loss source-Gram saturation while the edge is invisible
to the logical selectors.  A successful cell must violate at least one of
those hypotheses.  Concretely it must use one of:

1. an edge/infinite actuator carrying nontrivial logical selector action;
2. a genuinely matrix-only capacity-gated saturation estimate rather than
   an isotypic finite restriction table; or
3. a non-Bass--Serre additive/root decoder whose expanding label boundary is
   itself charged.

This is sharper than the general induction barrier: the unwanted selector
characters occur in the very target type which was supposed to remove them,
not merely in some other representation of the finite packet.
