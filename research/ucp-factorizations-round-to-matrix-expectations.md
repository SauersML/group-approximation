---
rg: 2
id: ucp-factorizations-round-to-matrix-expectations
kind: claim
title: Approximate UCP factorizations of bistochastic self-adjoint maps round to expectations in the original dimension
distinct_from:
  schur-near-idempotents-round-dimension-uniformly: That extracts a partition from a Schur symbol; this starts with a supplied abstract UCP factorization and applies to arbitrary self-adjoint bistochastic maps, with no common matrix-unit eigenbasis.
artifacts:
  - research/artifacts/ucp-factorization-to-same-dimension-expectation-2026-09-08.md
---

Let `P:M_d->M_d` be self-adjoint on normalized `L^2`, bistochastic,
and UCP. Suppose a finite-dimensional unital C*-algebra `B` and UCP
maps `Delta:B->M_d`, `Upsilon:M_d->B` are supplied. Put

```text
r=||Upsilon Delta-id_B||_(infinity->infinity),
s=||Delta Upsilon-P||_(infinity->2),       eta=2r+s.
```

There is a unital represented algebra `A subset M_d` with

```text
||P-E_A||_(infinity->2) <= min(2,44 eta^(1/4)).
```

Completely bounded upper bounds may be used for `r,s`. The constants
do not depend on either algebra's dimension or on representation
multiplicities. The final expectation acts in the original `M_d`.

Consequently every self-adjoint bistochastic UCP map with
`epsilon=||P^2-P||_cb` sufficiently small has such an expectation
at mixed-norm distance `O(epsilon^(1/4))`, with a universal constant.
This corollary uses Kitaev's UCP factorization theorem, not a claim
that its abstract factorization is already a represented expectation.

The native Kazhdan heat estimates provide small `infinity->2`
idempotence defect; they do not provide the completely bounded
hypothesis or the factorization above. No general mixed-norm
near-idempotent rounding theorem or nonhyperlinearity conclusion
is established here.

DERIVATION
stinespring-corner-repair-rounds-ucp-factorizations
