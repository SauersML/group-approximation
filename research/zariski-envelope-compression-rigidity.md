---
rg: 2
id: zariski-envelope-compression-rigidity
kind: claim
title: Compression preserves the algebraic envelope in every finite-dimensional representation
distinct_from:
  commutant-no-growth: That claim says compression creates no new commuting endomorphisms; this one says the compressed and uncompressed subgroups have the same Zariski closure, which determines the commutant and every other envelope-level invariant at once.
artifacts:
  - GroupApproximation/Algebra/ZariskiEnvelopeEndpoint.lean
  - GroupApproximation/Algebra/ZariskiClosedSubgroup.lean
  - GroupApproximation/Algebra/ZariskiDescendingChain.lean
  - GroupApproximation/Criterion/ClosedEnvelopeCompressionCore.lean
---

Let `rho : H -> GL(V)` be any finite-dimensional complex representation and
let `s L s^{-1} <= L`.  Then the Zariski closures in `GL(V)` coincide:

```text
closure_Z( rho(s L s^{-1}) )  =  closure_Z( rho(L) ).
```

An exact finite-dimensional representation sees the compressed subgroup and
the original subgroup as the **same algebraic object**.  Consequently every
invariant computed from the algebraic envelope agrees for the two: dimension,
component group, unipotent radical, reductivity, invariant tensors of the
envelope, and the commutant — commuting with a set of matrices is a
polynomial condition, so `rho(L)' = closure_Z(rho(L))'`, and
`commutant-no-growth` is the first shadow of this equality.  Any
finite-dimensional strategy for detecting a strict compression must
therefore work below the level of the algebraic hull, which is what
`noetherian-invariant-compression-rigidity` forbids for every equivariant
chain-condition invariant.
