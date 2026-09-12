---
rg: 2
id: root-block-piecewise-transport-cannot-host-nonce-bcs
kind: claim
title: A signed-Hecke atlas confined to one finite root block is already a forbidden finite-dimensional BCS model
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs stationary representation-type flows in graphs of finite groups; this is the direct algebraic obstruction to returning every transported context projection into one fixed finite simple corner.
  exact-five-fourths-projection-return-collapses-the-packet: that rules out an over-capacity projection inequality by canonical-trace conservation; this rules out even capacity-preserving context assembly when all images stay in a finite root algebra.
---

Let `B` be a unital star algebra of a finite BCS with no Connes-embeddable
tracial state.  Let `K` be finite and let `q in C[K]` be a nonzero projection.
There is no compatible projection atlas `(BPA1)--(BPA3)` all of whose
projections lie in the finite-dimensional corner

```text
q C[K] q.                                                  (RBT1)
```

Indeed such an atlas gives a unital star homomorphism

```text
A(B) -> q C[K] q                                           (RBT2)
```

by `bcs-corner-model-is-a-compatible-projection-atlas`.  Composing `(RBT2)`
with any faithful finite-dimensional representation of the corner and its
normalized matrix trace gives a Connes-embeddable tracial state on `A(B)`, a
contradiction.

In particular, start from the common hyperoctahedral context blocks of
`all-bcs-contexts-share-one-hyperoctahedral-signed-type`.  If piecewise HNN
transport sends every coordinate atom of every context copy to a projection
inside one root algebra `q_D C[K_D]q_D`, then the construction cannot realize
the no-CE BCS.  A successful signed-Hecke atlas must embed at least one
context block as a genuinely different finite-dimensional subalgebra of the
infinite corner `q_D C[Gamma]q_D`; merely permuting or unitarily rotating
atoms inside the root `M_D(C)` is insufficient.
