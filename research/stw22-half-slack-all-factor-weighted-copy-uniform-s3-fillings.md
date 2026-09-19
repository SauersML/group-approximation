---
rg: 2
id: stw22-half-slack-all-factor-weighted-copy-uniform-s3-fillings
kind: claim
title: Half-slack replicated weighted fibres in all finite factors have a universal three-sphere modulus
distinct_from:
  stw22-matrix-weighted-copy-codimension-two-uniform-s3-fillings: that theorem is the matrix branch and isolates the codimension-one obstruction; the present theorem uses half slack to exclude it and adds all diffuse II1 factors.
  stw22-diffuse-weighted-copy-uniform-s3-fillings: that theorem is the diffuse branch and only needs strict slack; the present theorem also includes every matrix factor in the half-slack regime needed for fibre-gap replication.
  stw22-all-finite-factor-weighted-copy-uniform-s2-fillings: that theorem is degree two and needs only strict slack; the present degree-three theorem imposes half slack because of the sharp matrix codimension-one obstruction.
artifacts:
  - research/artifacts/stw22-matrix-lc3-codimension-barrier-audit-2026-08-31.md
  - research/artifacts/stw22-dim4-factor-bundle-breakthrough-2026-08-31.md
---

Let `(N,tau)` be any finite factor with separable predual. Let `m>=2` and
let `a in N` be a positive contraction satisfying

```text
m tau(supp(a))<=1/2.                                   (AF4-1)
```

Give the exact weighted-copy fibre `F_(N,m)(a)` the Hilbert-sum
`2`-metric. Every continuous map `S^3->F_(N,m)(a)` contained in the ball
of radius

```text
rho_AF,3(epsilon)=min(epsilon,1)^3/216000000           (AF4-2)
```

about one point extends over `B^4` inside the concentric
`epsilon`-ball. The modulus is independent of factor type, matrix size,
II1 isomorphism class, copy number, and weight.

Every such fibre is three-connected. Together with the lower degree
theorems, the half-slack family is uniformly equi-`LC^3`.

A quantitative slack restriction such as half slack is essential to this
all-matrix-size statement; half slack is a convenient sufficient threshold,
not a uniquely necessary one. Under merely positive slack, matrix codimension-one fibres contain essential
`S^3` maps of normalized radius tending to zero.