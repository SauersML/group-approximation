---
rg: 2
id: lamp-telescope-base-is-lef
kind: claim
title: The lamp-by-telescope base is LEF
distinct_from:
  sofic-non-mf-witness: That claim is soficity of the whole witness `W`; this one upgrades soficity to LEF for the shift-free part `ClLamp(X) semidirect T`, which is strictly stronger and strictly smaller.
  literal-telescope-core-lef: That claim is the same property for the telescope core of the literal presented group `E`, whose lamp kernel is an infinite block amalgam containing free subgroups; this one is for the Clifford witness and its commuting-lamp quotient, whose lamp kernels are locally finite, so the proof needs no amalgam theory.
  literal-telescope-split-normal-form: That claim is the algebraic splitting of `E` over the telescope; this one is an approximation property of the corresponding subgroup of the witness.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
---

`ClLamp(X) semidirect T` and `F_2[X] semidirect T` are locally embeddable
into finite groups, hence sofic and — by `lef-implies-operator-mf` — operator
MF.  Each is the directed union of the residually finite groups
`L' semidirect Gbar_k` with `L'` a finite `Gbar_k`-invariant lamp subgroup.

Therefore both the witness and its commuting-lamp quotient are `Z`-extensions
of LEF groups:

```text
W        = (ClLamp(X) semidirect T) semidirect Z,
W/<zeta> = (F_2[X]    semidirect T) semidirect Z.
```
