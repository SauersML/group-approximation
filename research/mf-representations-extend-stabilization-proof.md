---
rg: 2
id: mf-representations-extend-stabilization-proof
kind: route
title: Both Hom sets are the same K1 Hom set and restriction is the identity
target: mf-representations-of-units-extend-under-stabilization
requires:
  - purely-infinite-unit-group-max-mf-quotient-is-k1
  - aut-of-projective-module-max-mf-quotient-is-k1
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

## Proof

Both `R^x` and `GL_n(R) = Aut_R(R_R^n)` have maximal MF quotient `K_1(R)`,
the first by the rank-one classification and the second by the projective
module version applied to `P = R_R^n`, whose endomorphism ring `M_n(R)` is
purely infinite simple and has `K_1(M_n(R)) = K_1(R)`.

So for an MF group `M`, composition with the two quotient maps gives
bijections

```text
Hom(K_1(R), M) --> Hom(R^x, M),
Hom(K_1(R), M) --> Hom(GL_n(R), M).
```

Under them, restriction along `iota_n` corresponds to the map induced by
`K_1` of `iota_n`, which sends the class of `diag(u,1,...,1)` to the class of
`u`, so it is the identity of `K_1(R)`.  A map that is the identity under
bijections on both sides is a bijection.
