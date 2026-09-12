---
rg: 2
id: cuntz-groupoid-admits-no-folner-sequence
kind: claim
title: The Cuntz groupoid of Thompson's V is not fiberwise amenable and has no Folner sequence
distinct_from:
  thompson-v-cantor-orbits-have-no-folner-sets: that bounds the boundary of finite point sets under V; this transfers the bound, with multiplicities, to finite subsets of the source fibres of the germ groupoid, which is the hypothesis of Ma's soficity theorem for full groups.
  thompson-v-covariant-cantor-representations-are-not-amenable: that excludes Bekka-amenable covariant unitary representations of the Cantor system; this is a counting statement about source fibres of the groupoid and involves no representation.
artifacts:
  - research/artifacts/thompson-v-soficity-stability-and-full-groups-2026-09-12.md
---

**ESTABLISHED.** Let `G_2` be the Deaconu--Renault groupoid of the one-sided 2-shift on
`X = {0,1}^N`, the Cuntz groupoid. It is ample, Hausdorff, second countable and minimal, with
compact unit space, and `V <= [[G_2]]` through the bisections `B_g` of prefix replacements.

Fix a finite generating set `S` of `V`, and let `c_S` be the constant of
`thompson-v-cantor-orbits-have-no-folner-sets`. For every compact `K` containing the bisections
`B_s`, `s in S`, and every finite `F <= G_2`,
```text
|K F \ F|  >=  (c_S / 2|S|) |F| .
```

Consequences, in the definitions of Xin Ma, *Fiberwise amenability of ample étale groupoids*,
arXiv:2110.11548v1 (read from the PDF):
1. `G_2` is not fiberwise amenable (Definition 3.10(1)).
2. `G_2` admits no Følner sequence (Definition 4.12).
3. Ma's Theorem 7.5 ("Let G be a second countable minimal groupoid that admits a Følner sequence.
   Then [[G]] is sofic.") and his Corollary D(1) therefore cannot certify that `V` is sofic. His
   approximations restrict the full group to finite range sets `r(T_n u_n)`, and Theorem 2 of the
   artifact shows that every such restriction keeps a fixed proportion of boundary.

The same count gives artifact Corollary 3.3: a finite model of `V` with an almost-equivariant
map to `X` has defect bounded below, with any multiplicity and whatever relations the model
satisfies.

Derivation: `cuntz-groupoid-admits-no-folner-sequence-proof`.
