---
rg: 2
id: leavitt-affine-omega-one-copy-picture-area-at-least-eight
kind: claim
title: Every affine-Omega one-copy relative picture has area at least eight
artifacts:
  - research/leavitt-affine-omega-picture-area-six-proof.md
  - research/artifacts/search-leavitt-affine-omega-relative-pictures.py
  - research/artifacts/search-leavitt-affine-omega-relative-pictures.sbatch
distinct_from:
  leavitt-degree-four-one-copy-picture-has-area-at-least-eight: that treats the revised composite-involution word, now known injective; this treats the distinct still-open affine Omega candidate with slots (r,1,a,c,1,e,q,p).
---

For the affine degree-four candidate

```text
W_8=r t^2 a t^(-1)c t^2 e t^(-1)q t p t,
```

no connected spherical relative picture with at most six orbit cells has all
but one coefficient region trivial and a nonidentity boundary in the
remaining coefficient copy.  In particular no such picture kills
`Omega(c_0,p_0)=x_15(s_0^2)_0` through area six.

Every orbit cell has odd stable-letter valence, so odd-area pictures are
impossible.  Therefore any one-copy kernel diagram for this still-open
candidate has area at least eight.
