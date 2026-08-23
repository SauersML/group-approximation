---
rg: 2
id: operator-norm-rank-monodromy-zero
kind: claim
title: A nontrivial cyclic rank ratio forces every finite-dimensional active carrier to vanish
distinct_from:
  trace-cyclic-rank-mismatch-checksum: that is a normalized-HS energy inequality robust under unequal trace reservoirs; this uses operator distance below one to obtain exact integer rank equations.
  finite-schur-clifford-packet-flexible-hs-exactification: that rounds finite packets in normalized HS norm; this is the discrete rank endpoint after actual projections and operator-norm transport have been authenticated.
artifacts:
  - research/artifacts/no-renormalization-adversarial-collision-compiler-2026-08-23.md
  - research/artifacts/finite-memory-self-hashing-non-mf-2026-08-23.md
  - GroupApproximation/Sofic/InvolutionRankMass.lean
  - GroupApproximation/Sofic/NoRenormalizationCapacity.lean
---

Orthogonal projections at operator distance strictly less than `1` have equal
rank. Thus a cyclic verifier whose selector transport is accurate below `1`
turns every approximate edge comparison into an exact integer equation.

If one traversal of a nonempty `k`-cycle yields

```text
a^k r=b^k r
```

for `a!=b`, then `r=0`.  The projection rigidity and integer endpoint are
machine-checked as `projection_rank_rigid` and
`rank_zero_of_power_monodromy`.  Constructing authenticated selector words
with these hypotheses is a separate compiler obligation.
