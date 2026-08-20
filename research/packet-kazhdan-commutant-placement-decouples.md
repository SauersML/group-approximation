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
mass, and represent the direct product on `H=H_sigma tensor H_rho`.

Put the whole packet on the second tensor factor.  It commutes exactly with
both `sigma(Lambda)` and `sigma(s Lambda s^(-1))`; scaled Kazhdan transport on
the first factor holds with zero error.  Nevertheless the packet Reynolds gap
is positive by `predicate-rank-jump-forces-adjoint-reynolds-gap`, and tensor
amplification does not change its normalized rank.

Consequently bare commutant placement cannot make the predicate defect pay.
A successful return transducer needs a coefficient-covariance relation tying
the Reynolds range to actual compressor conjugates.

