---
rg: 2
id: properly-infinite-unit-rank-two-normal-generator
kind: claim
title: One commutator normally generates the rank-two elementary group over a ring with a properly infinite unit
distinct_from:
  full-idempotent-ring-has-properly-infinite-unit: that is the ring-theoretic equivalence supplying the hypothesis; this is the group-theoretic normal-generation statement it feeds.
  leavitt-gl-equals-el-and-perfect-unit-group: that identifies the unit group with the elementary group and proves perfection for the binary Leavitt algebra using a complete prefix code; this needs only two half-orthogonal pairs, no exhaustion of the unit, and names one explicit normal generator with a conjugate count.
  chatterji-kassabov-normal-generator-embedding: that embeds a group into a two-generated group with a prescribed normal generator; this is an internal normal-generation statement about elementary groups over a ring.
artifacts:
  - research/artifacts/rank-two-descent-review-2026-09-07.md
---

Let `R` be unital with `v,w,a,b in R` satisfying

```text
wv = 1,   ba = 1,   bv = 0.
```

Then `1 + vb` is a unit,

```text
D = diag(1 + vb, 1) = [e_12(v), e_21(b)] in EL_2(R),
```

and the normal closure of `D` in `EL_2(R)` is all of `EL_2(R)`.  Every
elementary generator is a product of at most four conjugates of `D` or
`D^(-1)`, so for every homomorphism `rho` into a group with a
conjugation-invariant subadditive length,

```text
l(rho(e_(ij)(r))) <= 4 l(rho(D)).
```

No property (T) is used, and `EL_2(R)` is perfect whenever such elements
exist, the normal generator being itself a commutator.
