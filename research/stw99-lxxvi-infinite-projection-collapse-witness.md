---
rg: 2
id: stw99-lxxvi-infinite-projection-collapse-witness
kind: claim
title: Z-stabilization makes two formerly distinct compact classes Cuntz equivalent as infinite projections
artifacts:
  - research/artifacts/stw99-lxxvi-third-depth-audit-2026-08-30.md
---

There exist a separable pure C*-algebra `A` and projections `p,q` over `A`
such that

```text
[p] != [q] in Cu(A),
[p tensor 1_Z] = [q tensor 1_Z] in Cu(A tensor_min Z),
```

and the generated ideal after tensoring with Z is not stably finite.

This remains open.  It records the compact-collapse corridor not controlled
by ideal-local K0: Cuntz-equivalent infinite projections need not be
Murray--von Neumann equivalent and may retain different K0 classes.

## Attempts

Toeplitz boundary projections live in the stably finite compact ideal and so
cannot realize this mechanism.  Simple pure ideals also do not supply the
needed before/after behavior: the simple case of LXXVI is already positive.
Any example must therefore use a genuinely non-simple ideal in which
Z-tensoring changes finiteness/comparison of compact classes.  No explicit
mixed finite/infinite pure ideal with this behavior is known here.
