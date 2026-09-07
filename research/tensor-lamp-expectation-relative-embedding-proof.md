---
rg: 2
id: tensor-lamp-expectation-relative-embedding-proof
kind: route
title: Tensor the finite involution expectation to kill every off-subgroup coefficient
target: binary-coset-lamp-coefficient-forces-relative-embedding
requires: []
artifacts:
  - research/artifacts/tensor-swap-expectation-repair-2026-09-07.md
---

Lift the binary involution to exact matrix involutions `S_n` by spectral
rounding, keeping the canonical actor unitary lifts `U_n(g)`. The expectation
onto `B(S_n)={S_n}'` is `(X+S_n X S_n)/2` and satisfies

```text
||E_(B(S_n))(U_n(g))||_2^2
 =(1+Re tr(U_n(g)^* S_n U_n(g) S_n))/2.
```

Take `k` tensor copies of the actor and of this expectation. Multiplication
and subgroup-commutation errors grow at most linearly in `k`, whereas the
squared expectation norm is raised to the `k`th power. A diagonal choice
with initial errors at most `k^-3` yields a canonical group embedding and
vanishing conditional expectation on every group word outside the subgroup.
On subgroup words the expectation converges to the word itself. Extend the
expectation identity by 2-norm density to obtain the full scalar commuting
square.

The artifact proves all lift, trace, normalization, and diagonal estimates,
and verifies the binary coefficient for both ordinary and free coset wreaths.
The double consequence uses the explicit factor-swap block construction,
whose proof is also given in
`arithmetic-double-swap-extension-is-binary-coset-wreath`.
