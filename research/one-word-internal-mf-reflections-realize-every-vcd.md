---
rg: 2
id: one-word-internal-mf-reflections-realize-every-vcd
kind: claim
title: Singly generated internal MF radicals realize every positive virtual cohomological dimension
root: true
artifacts:
  - research/one-word-internal-mf-reflections-realize-every-vcd-proof.md
---

For every integer `m>=1`, the binary Leavitt unit group `U` contains a
finitely generated non-MF subgroup `K_m` with a split MF reflection

```text
pi_m:K_m->>Q_m,
Q_m=F_2 wr C_m,                                         (EV1)
Rad_MF(K_m)=ker(pi_m)=normalClosure_(K_m)(d_m),          (EV2)
vcd(Q_m)=m.                                             (EV3)
```

Here `C_1` is trivial.  For every normal subgroup `N` of `K_m`,

```text
cl_MF^(K_m)(N)=pi_m^(-1)(cl_MF^(Q_m)(pi_m(N))).          (EV4)
```

The kernel in `(EV2)` is simultaneously the finite residual, compact
residual, finite-dimensional unitary residual, and linear residual over
every field.  In particular,

```text
profiniteCompletion(K_m)~=profiniteCompletion(Q_m),
Bohr(K_m)~=Bohr(Q_m).                                   (EV5)
```

The groups `K_m` are pairwise nonisomorphic.  For every `m>=2`, their MF
reflections are not virtually free and do not have context-free word
problem.  Thus a single fixed involutive radical generator is compatible
with every positive virtual cohomological dimension of the completely
visible quotient.
