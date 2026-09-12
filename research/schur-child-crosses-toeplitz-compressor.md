---
rg: 2
id: schur-child-crosses-toeplitz-compressor
kind: claim
title: Every Schur packet child crosses an explicit property-T Toeplitz compressor
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  schur-packet-child-square-is-pauli-transverse: that computes the finite packet diamond abstractly; this embeds one child/full edge across a concrete proper self-image of an infinite property-T group.
  truncated-weyl-two-chart-boundary: that realizes two local polynomial charts but has no property-T ambient group; this supplies a property-T elementary-group ambient compressor.
---

Fix a Schur--Clifford packet `A_f<=B_f` and its child

```text
B_f^Q=<A_f,q_(N+1)> < B_f.
```

For some fixed `r`, there is an injective homomorphism

```text
iota:B_f -> EL_r(T),
```

where `T` and `sigma` are from `toeplitz-head-tail-unital-self-embedding`,
such that

```text
iota(B_f^Q) <= EL_r(sigma(T)),
iota(p_(N+1)) notin EL_r(sigma(T)).                           (SCT1)
```

After increasing `r` if necessary, `Gamma=EL_r(T)` is a finitely generated
property-`(T)` group and entrywise application of `sigma` gives a proper
injective endomorphism `alpha` with

```text
alpha(Gamma)=EL_r(sigma(T)).                                  (SCT2)
```

Thus the finite predicate packet is not merely attached to an abstract
compressor: its `Q` child lies on the compressed side and its missing Pauli
generator lies on the uncompressed side of one explicit universal-lattice
compressor.

This is an algebraic placement theorem only. It does not assert that the
whole adjoint Reynolds difference survives the action of the remaining
elements of `alpha(Gamma)`; that exact quantitative issue is isolated by
`residual-action-can-erase-local-reynolds-density`.

