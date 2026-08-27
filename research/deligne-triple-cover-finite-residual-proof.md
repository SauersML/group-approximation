---
rg: 2
id: deligne-triple-cover-finite-residual-proof
kind: route
title: Deligne kills the centre and congruence quotients separate everything outside it
target: deligne-triple-cover-finite-residual-is-center
requires:
  - deligne-triple-cover-fd-central-invisibility
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
---

The prerequisite says every finite-dimensional unitary representation of
`E_3` kills `z`.  In particular every homomorphism to a finite group kills
`z`, after composing with the faithful regular unitary representation of the
finite target.  Hence `C_3 <= Res_fin(E_3)`.

Conversely, take `x notin C_3`.  Its image `g` in `Sp_4(Z)` is not the
identity.  Some integral entry of `g-I` is nonzero; choose an integer `m>=2`
not dividing that entry.  Reduction modulo `m` is a homomorphism

```text
Sp_4(Z) -> Sp_4(Z/mZ)
```

to a finite group and does not kill `g`.  Its composite with
`E_3 -> Sp_4(Z)` does not kill `x`.  Therefore
`Res_fin(E_3) <= C_3`, proving equality.
