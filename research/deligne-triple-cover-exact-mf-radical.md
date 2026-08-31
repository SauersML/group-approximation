---
rg: 2
id: deligne-triple-cover-exact-mf-radical
kind: claim
title: The MF radical of Deligne's triple cover is exactly its order-three center
goal: true
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  deligne-triple-cover-finite-residual-is-center: that computes the intersection of kernels of finite quotients; this computes the smaller intersection of kernels of all norm-matrix-corona representations.
  deligne-triple-cover-central-generator-is-mf-radical: that is the hard inclusion C_3 <= Rad_MF(E_3); this packages it with the unconditional reverse inclusion to give the exact radical.
---

For Deligne's connected triple cover

```text
1 -> C_3 -> E_3 -> Sp_4(Z) -> 1
```

one has

```text
Rad_MF(E_3) = C_3.                                     (DER1)
```

In particular, for either generator `z` of `C_3`,

```text
z in Rad_MF(E_3).                                      (DER2)
```

## Attempts

- The reverse inclusion is unconditional:
  `Rad_MF(E_3) <= Res_fin(E_3)=C_3`.  The forward inclusion is exactly
  `deligne-triple-cover-central-generator-is-mf-radical`.
- Because `C_3` has prime order and the universal MF quotient detects
  triviality of the radical, `(DER1)` is equivalent to the open claim that
  `E_3` is not MF.  Finite-dimensional invisibility alone does not establish
  this asymptotic operator-norm assertion.
- `deligne-triple-cover-mf-radical-dichotomy` now records the unconditional
  result: the radical is either `1` or the order-three covering kernel
  `C_3`.  The nontrivial branch is equivalently the open point-norm sector
  exclusion `deligne-nontrivial-maslov-opnorm-sectors-are-empty`.
