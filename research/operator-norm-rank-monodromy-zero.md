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
  - GroupApproximation/Sofic/CollisionCapacityDetectors.lean
---

Orthogonal projections at operator distance strictly less than `1` have equal
rank. Thus a cyclic verifier whose selector transport is accurate below `1`
turns every approximate edge comparison into an exact integer equation.

In full generality, let nonzero carrier projections `P_i` have ranks `r_i`,
and let selector projections `e_i,f_i<=P_i` have exact positive rational
rank fractions

```text
rank(e_i)=alpha_i r_i,             rank(f_i)=beta_i r_i.
```

If unitaries satisfy

```text
||U_i e_i U_i^*-f_(i+1)||_op<1
```

around a finite cycle, then

```text
prod_i alpha_i=prod_i beta_i.                          (ORM1)
```

Consequently unequal products force at least one carrier to vanish (and
force all of them to vanish when the edge equations connect their ranks).
For a coarse `M_2` selector returned cyclically to a fine `M_4` selector,
`alpha_i=1/2`, `beta_i=1/4`, so a nonzero cycle is impossible.

The previously recorded constant-ratio specialization is: if one traversal
of a nonempty `k`-cycle yields

```text
a^k r=b^k r
```

for `a!=b`, then `r=0`.  The projection rigidity and integer endpoint are
machine-checked as `projection_rank_rigid` and
`rank_zero_of_power_monodromy`.  Constructing authenticated selector words
with these hypotheses is a separate compiler obligation.
