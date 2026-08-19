---
rg: 2
id: finite-selector-gadget-induction-barrier
kind: claim
title: Finite group gadgets cannot prune characters of a commuting marked selector subgroup
artifacts:
  - research/artifacts/finite-selector-induction-barrier-2026-08-18.md
---

Let `H` be a finite group, let `J in Z(H)` be a central element, and let
`A <= H` be an abelian subgroup containing `J`.  Then **every** unitary
character

```text
chi : A -> T
```

with a prescribed value `chi(J)=zeta` occurs in the restriction to `A` of some
finite-dimensional unitary representation `pi` of `H` on which

```text
pi(J)=zeta I.
```

Indeed one may take the induced representation `Ind_A^H chi`.

Consequently, if commuting selector involutions together with the central mark
lie in `A`, no additional relations coming from a **finite noncommutative group
gadget** `H` can rule out one joint selector character compatible with the mark
while permitting another.  For example, if the mark relation only fixes odd
selector parity, a finite gadget cannot retain the one-hot odd characters and
remove the three-hot odd characters: every odd character of the selector
subgroup appears in a marked finite-dimensional representation.

This strengthens `one-hot-selector-parity-barrier` and
`affine-auxiliary-control-flow-barrier`: adding a finite noncommutative group
around the commuting selector bits still does not provide spectral selection.
A successful selector mechanism must leave at least one hypothesis of this
induction argument -- for example by being infinite with infinite-index
selector subgroup, by using a trace/corner condition rather than bare group
relations, or by avoiding a commuting selector subgroup containing the mark.
