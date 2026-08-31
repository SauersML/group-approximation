---
rg: 2
id: stw22-half-slack-matrix-diffuse-s3-dichotomy-proof
kind: route
title: Use half slack to remove the matrix SU2 obstruction and take the two type moduli
target: stw22-half-slack-all-factor-weighted-copy-uniform-s3-fillings
requires:
  - stw22-matrix-weighted-copy-codimension-two-uniform-s3-fillings
  - stw22-diffuse-weighted-copy-uniform-s3-fillings
artifacts:
  - research/artifacts/stw22-dim4-factor-bundle-breakthrough-2026-08-31.md
---

Every finite factor is either a normalized matrix algebra or diffuse II1.

In the diffuse case, (AF4-1) is strict slack, so
`stw22-diffuse-weighted-copy-uniform-s3-fillings` gives

```text
rho_diff,3(epsilon)=epsilon_0^3/216000000,
epsilon_0=min(epsilon,1),                              (AF4-3)
```

and global three-connectivity.

In the matrix case write `N=M_n`, `r=rank(supp(a))`,
`k=mr`, and `c=n-k`. If `a=0`, the fibre is a singleton. If `a!=0`, then
`r>=1` and, because `m>=2`,

```text
2<=k<=n/2,       c=n-k>=n/2>=2.                       (AF4-4)
```

Thus the codimension-two matrix theorem applies. Its modulus
`epsilon_0^3/276480` is larger than (AF4-3), and its fibres are globally
three-connected.

Hence (AF4-3) works in both cases. Taking degreewise minima with the
already universal path, loop, and two-sphere moduli yields one
equi-`LC^3` family. This is a pointwise dichotomy with one numerical
control; no continuity of factor type or matrix size is required.