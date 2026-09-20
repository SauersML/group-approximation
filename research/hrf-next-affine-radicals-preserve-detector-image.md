---
rg: 2
id: hrf-next-affine-radicals-preserve-detector-image
kind: claim
title: Cohomologically rigid split elementary-abelian radicals preserve the edge-twist detector image
distinct_from:
  edge-twist-extensions-of-triangle-colimits-moment-test: that tests virtual splitting through cellular moments on finite covers; this compares central-extension lift discrepancies for a split affine finite quotient and its base under explicit module cohomology hypotheses
artifacts:
  - research/artifacts/hrf-next-attack-2026-09-20.md
---

Let `p` be odd, `k=F_p`, and let `Lambda` be a nonpositively curved
triangle colimit with trivial face group, finite perfect vertex groups
`A_i`, and `H^2(A_i;k)=0`. Let

```
f: Lambda ->> Q=V semidirect S,
g: Lambda ->> S
```

be a finite quotient and its projection, with `V` a finite-dimensional
`kS`-module. Suppose

```
H^1(S;V*)=0 and H^1(A_i;V)=0 for each vertex i,
```

where the vertex action is through `g|A_i`, and `V*` is the dual module.
Orient each edge from vertex i to vertex j. Define
`D_f:H^2(Q;k)->direct-sum_e Hom(E_e,k)` as follows: in a central
extension representing `beta`, lift the maps from `A_i` uniquely
and write their edge discrepancy as `s_i(x)=z^(d_e(x))s_j(x)`.
Then `D_f(beta)=(d_e)_e`; define `D_g` identically. These maps are
well-defined and linear, and

```
D_f(beta)=D_g(res_S beta) for every beta in H^2(Q;k),
image D_f=image D_g.
```

In particular, if `H^2(S;k)=0`, then `D_f=0` even though `Q` may have
cyclic p-composition factors and new Schur-multiplier classes. Each
vertex `H^1` vanishing can be weakened to the actual affine cocycle of
`f|A_i` being a coboundary. No classification of all finite quotients,
persistence assertion, or hyperbolic counterexample follows.

Proof: [[hrf-next-affine-radicals-preserve-detector-image-proof]].
