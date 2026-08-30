---
rg: 2
id: stw99-lxxvi-z-stable-unitary-kernel-proof
kind: route
title: Compare scalar stabilization with Jiang's weak equivalence of matrix unitary groups
target: stw99-lxxvi-z-stabilization-kills-unstable-unitary-kernel
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Put `E=D tensor_min Z`.  Then `E` and every matrix algebra over `E` are
Z-stable.  Jiang, Theorem 2.8 in
[Nonstable K-theory for Z-stable C*-algebras](https://arxiv.org/abs/math/9707228),
proves that every canonical matrix-stabilization map between their unitary
groups induces isomorphisms on all homotopy groups.  Hence

```text
pi_k(U(M_n(E))) -> pi_k(U(M_infinity(E)))              (1)
```

is injective.

The image of the scalar extension of `alpha` under (1) is the scalar
extension of the stable image of `alpha`.  The latter is zero by hypothesis.
Injectivity of (1) therefore makes the original class zero already in
`pi_k(U(M_n(E)))`.
