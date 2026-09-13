---
rg: 2
id: product-states-approximate-high-degree-2-local
kind: claim
title: Product states approximate the ground energy of 2-local Hamiltonians on D-regular graphs to within 12(d^2 ln d / D)^(1/3)
artifacts:
  - research/artifacts/qpcp-landscape-sources-2026-09-12.md
distinct_from:
  quantum-pcp-constant-gap-local-hamiltonian: that is the hardness conjecture at constant locality; this is a classical-witness upper bound for 2-local instances whose constraint graph has large degree, which bounds the degree any 2-local hard family can have unless QMA is in NP.
---

**ESTABLISHED BY CITATION** (Brandao--Harrow, arXiv:1310.0017v2, Corollaries 4
and 5).

Let `G=(V,E)` be a `D`-regular graph on `n` vertices and

```text
H = E_((i,j) in E) H_ij = (2/(nD)) sum_((i,j) in E) H_ij,   ||H_ij|| <= 1,
```

with `H_ij` acting on the `d`-dimensional particles `i,j`. Then some product
state `phi = phi_1 tensor ... tensor phi_n` satisfies

```text
tr(H phi) <= e_0(H) + 12 (d^2 ln(d) / D)^(1/3).                     (PS1)
```

Consequently, if `beta-alpha >= 12(d^2 ln(d)/D)^(1/3)+delta`, the promise problem
`e_0(H)<=alpha` versus `e_0(H)>=beta` has classical witnesses of length
`O(nd log(n/delta))` for the first case, checked in time `nDd^4 polylog(1/delta)`.

**Bearing on the root.** If QMA is not contained in NP, a QMA-hard family of
2-local `D`-regular instances at promise gap `gamma` must have
`D < 1728 d^2 ln(d)/gamma^3`. The source also proves a clustered version
(Theorem 6, Corollary 7): small average block expansion or sub-volume block
entanglement gives witnesses of size `O(n 2^m log(1/delta))`. It notes that its
technique needs `n^(k-1)/eps^(O(1))` terms for `k>2`, so the degree bound does
not constrain `k`-local families with `k>=3` at bounded degree. Perturbative
gadgets do not transfer it, because they create constant-degree vertices.
