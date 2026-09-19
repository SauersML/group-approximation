---
rg: 2
id: packet-kazhdan-commutant-placement-decouples
kind: claim
title: Commutant placement alone leaves the predicate Reynolds gap tensor-decoupled from Kazhdan transport
artifacts:
  - research/artifacts/schur-clifford-predicate-rank-compiler-2026-08-19.md
distinct_from:
  nonmonomial-multiplicity-obstructs-hs-compressor-transport: that uses a nonmonomial finite quotient to refute permutation transport of fine Kazhdan blocks; this leaves Kazhdan transport completely valid and shows an independent coefficient packet can retain its Reynolds defect on another tensor factor.
  multiplicity-surplus-is-blind-to-the-non-ce-input: that uses a classical unsatisfiable CSP to refute beta-only return arguments; this is an exact representation countermodel to the narrower proposal of coupling a packet merely by commutation with the compressed and uncompressed Kazhdan subgroups.
---

Let `Lambda` be a group with a one-sided compressor `s`, and let `sigma` be
any finite-dimensional exact representation of `<Lambda,s>`.  Let `rho` be an
exact representation of a predicate packet `B_f` carrying positive forbidden
mass, and represent the direct product on

```text
H=H_sigma tensor H_rho.
```

Put the whole packet, hence both `A_f` and `B_f`, on the second tensor factor.
Then it commutes exactly with both `sigma(Lambda)` and
`sigma(s Lambda s^(-1))`; every hypothesis and conclusion of scaled Kazhdan
transport on the first factor holds with zero error.  Nevertheless the packet
Reynolds projections satisfy

```text
rank(R_A-R_B)/dim(H_rho)^2 > 0
```

by `predicate-rank-jump-forces-adjoint-reynolds-gap`, and tensor amplification
does not remove that normalized rank gap.

Consequently, relations saying only that `A_f` centralizes `Lambda` and
`B_f` centralizes the compressed subgroup cannot make the predicate defect
pay.  A successful return transducer needs a **coefficient-covariance**
relation tying named packet generators or their Reynolds range to actual
compressor conjugates; that relation must visibly fail in this tensor-product
model.
