---
rg: 2
id: affine-selector-clifford-proves-derived-reset-bridge
kind: route
title: Combine gauge covariance with the affine Clifford reset packet
target: derived-lifted-gauge-reset-spin-bridge
requires:
  - gauge-doubling-gives-selector-flip-symmetries
  - affine-selector-clifford-residual-packet
  - affine-selector-clifford-rank-swap-balanced
---

Gauge doubling makes the reset act only on two private shares while fixing
their logical product, every lifted BCS constraint, and the native signal.
The direct-sum gauge orbit supplies exact covariant marked completeness.

The affine selector Clifford packet realizes every rank-fifteen residual form
and the derivative reset in one finite ordinary-word table.  The actual gauge
translation is a commutator by `(ACR2)`, commutes with the common residual,
and changes the selector signs by `(ACP7)`.  The inert dummy qubit is the
missing hyperbolic pair.  After all four old or fresh semantic selector signs
are fixed, both sides restrict to exactly `2 rho_15`; hence the relevant
restriction matrices, rather than merely the coarse reset-sign totals, agree.

For the incoming S3 radical chart, tensor this fixed auxiliary packet with
the common reset type `rho_(L_i)`.  Both ambient chart simples already
restrict to one copy of `rho_(L_i)`; after tensoring, old and new sides both
restrict to the single common type

```text
rho_(L_i) tensor rho_15
```

with the same factor-two rank-swap multiplicity.  This one-time fixed
stabilization multiplies every local dimension by the same constant and
therefore leaves the normalized type-vector payment unchanged.  It does not
assume that the predicate-dependent `L_i` itself has rank fifteen.

Exactify this one fixed finite Clifford table and align its fixed overlap
blocks.  Finite-group flexible Hilbert--Schmidt stability and polar alignment
give `O(sqrt(E))` loss with constants independent of ambient multiplicity.
Take the graph of finite groups whose middle vertex is `C_20`, whose left and
right edge groups are respectively the old and fresh semantic
selector--residual groups, and whose outer vertices are the old and next
rank-sixteen Schur packets.  The selected outer spin types and the natural
`C_20` type have the identical edge restriction `2 rho_15` just computed.
The normal-form theorem for amalgams embeds both outer marked bases; on an
exact completeness model, countable amplification absorbs the finite factor
two and extends the representation across the graph.  In finite matrices,
fixed finite-group exactification followed by polar alignment on these equal
edge multiplicities gives the asserted `O(sqrt(E))` loss.

These statements prove the five clauses of
`derived-lifted-gauge-reset-spin-bridge` without using a signed-permutation
conjugacy between a diagonal sign and a translation.
