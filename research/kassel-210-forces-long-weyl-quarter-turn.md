---
rg: 2
id: kassel-210-forces-long-weyl-quarter-turn
kind: claim
title: Kassel relation 2.10 forces the long-root Weyl word to rotate three positive root groups by a quarter-turn
artifacts:
  - research/artifacts/kassel-210-forces-weyl-quarter-turn-2026-08-21.md
distinct_from:
  kassel-210-is-first-s5-order-three-seam: that is a finite S5 orbit computation; this is an exact representation-independent group identity.
  long-root-central-product-has-exact-maslov-models: that treats two commuting rank-one factors; this uses the first mixed relation linking the negative long root to short roots.
  maslov-mod3-projective-defect-gap: that requires collapse of the scalar marked sector; this centralizes only three positive-root generators and does not yet control the opposite long-root pair.
---

Assume Kassel's commuting-root relations and (2.4), (2.5), (2.10). For

```text
w=x_beta x_(-beta)^(-1) x_beta
```

one has the exact identities

```text
w x_alpha w^(-1)=x_(alpha+beta)^(-1),
w x_(alpha+beta) w^(-1)=x_alpha,
w x_(2alpha+beta) w^(-1)=x_(2alpha+beta).
```

Consequently `w^4` centralizes all three displayed positive-root generators.
The bounded derivation also yields dimension-free normalized-HS commutator
estimates from the corresponding relator defects. It does not yet centralize
`x_beta` or `x_(-beta)`.

The latter pair is closed exactly by
`kassel-rank-one-braid-closes-central-mark`, the braid form of Kassel
Lemma 2.2.
