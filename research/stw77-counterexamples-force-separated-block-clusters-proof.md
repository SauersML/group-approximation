---
rg: 2
id: stw77-counterexamples-force-separated-block-clusters-proof
kind: route
title: Compare the merge estimate with the positive centralization defect
target: stw77-counterexamples-force-separated-block-clusters
requires:
  - oinfty-map-stability-is-central-isometry-splitting
  - stw77-near-duplicate-fd-blocks-merge
---

Because `phi` is not O-infinity-stable, the central-isometry criterion gives
a finite set of contractions `a_1,...,a_m` for which

```text
gamma=kappa_phi({a_1,...,a_m})>0.
```

Suppose an approximating tuple and a proper-support clustering had all
coordinate variations strictly below `3 gamma/8`. The merge lemma would give
orthogonal isometries `s_1,s_2` satisfying

```text
max_(l,t)||[s_t,x_l]|| < 3 gamma/4.
```

Since `||x_l-phi(a_l)||<gamma/8`, the triangle inequality would give

```text
max_(l,t)||[s_t,phi(a_l)]||
 < 3 gamma/4+2(gamma/8)=gamma,
```

contradicting the definition of `gamma`. This proves the asserted uniform
separation.
