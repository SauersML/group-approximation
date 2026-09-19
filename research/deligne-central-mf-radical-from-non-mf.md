---
rg: 2
id: deligne-central-mf-radical-from-non-mf
kind: route
title: Squeeze a nontrivial MF radical into the prime-order Deligne centre
target: deligne-triple-cover-central-generator-is-mf-radical
requires:
  - deligne-triple-cover-is-not-mf
  - deligne-triple-cover-finite-residual-is-center
  - universal-mf-quotient
---

Every finite group is MF, so every finite quotient is among the detectors
whose kernels contain `Rad_MF`.  Consequently

```text
Rad_MF(E_3) <= Res_fin(E_3) = C_3.
```

If `E_3` is not MF, `universal-mf-quotient` says its MF radical is nontrivial.
The only nontrivial subgroup of the prime-order group `C_3` is `C_3` itself.
Thus `Rad_MF(E_3)=C_3`, and in particular its generator `z` belongs to the
MF radical.
