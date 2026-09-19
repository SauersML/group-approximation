---
rg: 2
id: scaling-unimodular-racg-blocks
kind: claim
title: Exact unimodular RACG blocks at every scaling factor
distinct_from:
  prime-scaling-maximal-kazhdan-blocks: that claim uses complete finite Clifford blocks only at prime scales; this computes the noncomplete graph-Clifford blocks for every integer scale.
artifacts:
  - research/artifacts/composite-scaling-kazhdan-radical-reconstruction-2026-08-30.md
---

For every integer `m>=2`, each connected component of the scaling-family
orbital graph is the Cayley graph `Gamma_m` on

```text
X_m=(Z/mZ)^3,
x adjacent to y  iff  x-y is unimodular modulo m.
```

Equivalently, for every prime `p|m`, the reductions of `x` and `y` in
`F_p^3` are different.  The graph has

```text
|X_m|=m^3,
degree=m^3 product_(p|m) (1-p^(-3)),
omega(Gamma_m)=ell(m)^3,
```

where `ell(m)` is the least prime divisor of `m`.  Under CRT it is the
categorical product of complete `p^3`-partite graphs, with part size
`p^(3(e-1))` for `p^e||m`.

The block lamp group is the central graph-Clifford extension

```text
1 -> <w> -> P_m -> W_(Gamma_m) -> 1,
```

where `W_(Gamma_m)` is the right-angled Coxeter group on `Gamma_m`.
The full lamp kernel is the free product of the `P_m`-blocks amalgamated
over their common central involution, and the full group has the one-edge
Bass--Serre decomposition

```text
E_m=(V_m x <w>) *_(B_(m,1) x <w>) (P_m semidirect B_(m,1)).
```

DERIVATION
[[scaling-unimodular-racg-blocks-proof]]
