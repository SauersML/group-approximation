---
rg: 2
id: mf-finite-normal-tracially-visible
kind: claim
title: Finite normal subgroups of an MF group are tracially visible
distinct_from:
  finite-normal-compression-obstruction: That claim kills a finite normal subgroup in every norm-matrix-corona representation of a Kazhdan-compression group; this one says that in any MF group a finite normal subgroup which survives one corona representation is visible to normalized traces.
  mf-implies-hyperlinear: This settles only the elements of finite normal subgroups; the root claim asks for every nontrivial element.
  finite-infranormal-subgroup-is-normal: That claim is a purely group-theoretic normality statement about infranormal subgroups; this one is an analytic visibility statement about traces of corona models.
artifacts:
  - GroupApproximation/Sofic/MFDefinitions.lean
---

Let `G` be a countable MF group (weak norm-matrix-corona convention) and let
`K` be a finite normal subgroup of `G`.  Then every `g != 1` in `K` is
tracially visible in the sense of `hyperlinear-elementwise-visibility`, with
the explicit constant

```text
c_g >= c(K)/|K|,
c(K) = min{ 1-Re(chi_sigma(h)/sigma(1)) : sigma in dual(K), h in K,
            sigma(h) != 1 } > 0.
```

In particular no nontrivial element of a finite normal subgroup of an MF
group lies in the hyperlinear residual: the torsion-central mechanism which
produces non-MF groups can never produce a nonhyperlinear one.
