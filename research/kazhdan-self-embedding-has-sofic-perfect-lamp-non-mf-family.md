---
rg: 2
id: kazhdan-self-embedding-has-sofic-perfect-lamp-non-mf-family
kind: claim
title: A residually finite Kazhdan self-embedding yields conditional sofic non-MF ordinary perfect-lamp groups
distinct_from:
  wreath-compression-mf-radical: that also computes an abelianized lamp quotient and treats abelian lamps; this proves the perfect-lamp case by a direct commuting-corner argument and gives an elementary sofic model under finite-index self-embedding.
  finite-block-perfect-lamps-have-exact-mf-radical: that constructs free products of finite blocks and proves finite presentability; this concerns the ordinary restricted direct-sum lamp group and makes no finite-presentability assertion.
artifacts:
  - research/artifacts/compression-locally-finite-centralizer-criterion-2026-09-08.md
  - research/artifacts/affine-perfect-lamp-wreath-recheck-2026-09-08.md
---

Suppose `Lambda` is countable, residually finite, and has property
`(T)`, and `phi:Lambda->Lambda` is injective with proper finite-index
image. Let `N` be its direct limit, `H=N semidirect Z`, and `L` the
initial copy of `Lambda`, with the generator `u` acting so that
`uLu^-1=phi(L)<L`. For any nontrivial finite perfect group `B`,

```text
W=B^(H/L) semidirect H
```

is sofic and is not MF. Every norm-corona homomorphism kills its
entire lamp subgroup. This lamp subgroup has no nontrivial finite
subgroup normal in `W`. The ambient group `W` fails property `(T)`
because it maps onto `Z`; its non-MF proof still uses property `(T)`
for `L`.

If additionally `H` is residually finite, then

```text
Rad_MF(W)=D_W(L)=B^(H/L),
```

where `D` is the intrinsic compression-centralizer defect defined
in Section 7 of the artifact. Residual finiteness of `H` is a
separate displayed hypothesis for this equality.

All these assertions are conditional on the hypotheses. No concrete
arithmetic base or external property-`(T)` theorem is imported.

DERIVATION
perfect-lamp-compression-and-finite-orbit-sofic-proof
