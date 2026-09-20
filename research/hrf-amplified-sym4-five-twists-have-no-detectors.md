---
rg: 2
id: hrf-amplified-sym4-five-twists-have-no-detectors
kind: claim
title: Every stable Sym4 amplification fails to detect a nonzero central five-twist of the pinned PSL2(19) triangle
distinct_from:
  hrf-break-sym4-five-twists-have-no-detectors: that excludes only scalar multiplicity one by commutative polynomial identities; this excludes every multiplicity with noncommuting blocks through explicit associator-unit certificates
artifacts:
  - research/artifacts/hrf-amplified-2026-09-20.md
  - research/artifacts/hrf-amplified-certificates.json
  - research/artifacts/hrf-amplified-verify.py
  - research/artifacts/hrf-amplified-linear-probe.py
---

Let `S=PSL_2(F_19)` and `rho=Sym^4` of its natural lifted
two-dimensional representation. Pin the three triangle edge generators
by the classes of

```
x12=[[2,11],[16,3]], x13=[[5,11],[4,9]], x23=[[6,15],[12,8]].
```

For `d in F_5^3 minus {0}`, let `Lambda_d` have three canonical
`S` vertices, a central `Z` with `Z^5=1`, and edge relations
`s_i(xij)=Z^(dij)s_j(xij)`.

For every algebraically closed field `K` of characteristic 19 and
every `m>=1`, there is no homomorphism `Lambda_d -> GL_(5m)(K)`
which takes `Z` to a nontrivial scalar and restricts on all three
vertices to conjugates of `rho tensor I_m`.

The obstruction holds with arbitrary noncommuting multiplicity
intertwiners and over all extension fields, not merely over tested
finite fields or for bounded `m`. It excludes no mixed-constituent
vertex representation and establishes neither a persistent central
twist nor a non-residually-finite hyperbolic group.

Proof: [[hrf-amplified-sym4-five-twists-have-no-detectors-proof]].
