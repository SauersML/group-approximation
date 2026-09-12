---
rg: 2
id: unnamed-return-via-fixed-rectangular-kernel
kind: route
title: Use rectangular rank-nullity as a model-dependent Hilbert-hotel carrier
target: unnamed-fixed-space-wandering-promotion
requires:
  - fixed-rectangular-kernel-unnamed-return-compiler
---

Given `(FRC1)`, let `P_U` be the kernel projection of `A(U)`.  Ordinary
rank-nullity gives normalized block density at least `(p-q)/p`, while a
fixed derivation of `(FRC1)` gives

```text
||(I_p tensor (w(U)^2-1))P_U||_2=o(1).
```

The block diagonal word has the same normalized scalar moments as `w(U)^2`,
so the Fejer argument for `unnamed-positive-density-fixed-space-is-terminal`
applies without naming or synchronizing `P_U`.

The route is invalidated: the required fixed factorization cannot coexist
with infinite order.
