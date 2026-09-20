---
rg: 2
id: hrf-break-sym4-five-twists-have-no-detectors
kind: claim
title: The pinned PSL2(19) triangle has no nonzero central five-twist detector with conjugate Sym4 vertices in characteristic 19
distinct_from:
  hrf-next-affine-radicals-preserve-detector-image: that excludes a split elementary-abelian radical under module cohomology hypotheses; this completely excludes one concrete five-dimensional characteristic-19 representation family by exact polynomial identities
artifacts:
  - research/artifacts/hrf-breakthrough-2026-09-20.md
  - research/artifacts/hrf-breakthrough-2026-09-20-certificates.json
  - research/artifacts/hrf-breakthrough-2026-09-20-verify.py
  - research/artifacts/hrf-breakthrough-2026-09-20-all-twists.py
  - research/artifacts/hrf-breakthrough-2026-09-20-sym4.py
---

Let `S=PSL_2(F_19)` and let `Lambda` be the triangle colimit of three
copies of `S` with trivial face group and cyclic edges identified by
the classes of

```
x12=[[2,11],[16,3]], x13=[[5,11],[4,9]], x23=[[6,15],[12,8]].
```

For any nonzero central twist `d in F_5^3`, let `Lambda_d` be the
colimit of the central five-twist with edge relation
`s_i(xij)=Z^(dij)s_j(xij)` and central `Z^5=1`.
Let `K` be an algebraically closed field of characteristic 19.

There is no homomorphism `Lambda_d -> GL_5(K)` sending `Z` to a
nontrivial scalar and restricting on each canonical `S` vertex to a
conjugate of the representation `Sym^4` of the natural `SL_2(F_19)`
module. In particular no finite field of characteristic 19 supplies
a detector of this form.

The certificate covers all 124 nonzero triples individually and all
extension fields, using exact polynomial unit-ideal identities. This
does not exclude other dimensions, characteristics, vertex representation
types, or arbitrary finite detectors, and proves no persistent twist.

Proof: [[hrf-break-sym4-five-twists-have-no-detectors-proof]].
