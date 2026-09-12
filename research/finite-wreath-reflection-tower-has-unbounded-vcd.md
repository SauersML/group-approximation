---
rg: 2
id: finite-wreath-reflection-tower-has-unbounded-vcd
kind: claim
title: One Leavitt MF black hole contains internal reflections of unbounded virtual cohomological dimension
root: true
artifacts:
  - research/finite-wreath-reflection-tower-has-unbounded-vcd-proof.md
---

Let `U=L_(F_2)(1,2)^x`.  There are finitely generated subgroups `K_n<=U`
and residually finite groups `Q_n`, `n>=0`, such that

```text
Q_0=F_2,                    Q_(n+1)=Q_n wr C_2,          (FWT1)
R_MF(K_n)~=Q_n,             Rad_MF(K_n)=B_n,            (FWT2)
vcd(Q_n)=2^n.                                              (FWT3)
```

Every `B_n` is normally generated in `K_n` by one fixed involution.  For
every normal subgroup `N` of `K_n`,

```text
cl_MF^(K_n)(N)=pi_n^(-1)(cl_MF^(Q_n)(pi_n(N))).          (FWT4)
```

The MF, finite, compact, finite-dimensional unitary, and linear residual over
every field are all equal to `B_n`.  Hence

```text
profiniteCompletion(K_n)~=profiniteCompletion(Q_n),
Bohr(K_n)~=Bohr(Q_n).                                   (FWT5)
```

The groups `K_n` are pairwise nonisomorphic.  For `n>=1`, their MF
reflections are not virtually free and do not have context-free word problem.
Thus finite block self-similarity pushes the internal reflection calculus
strictly beyond the prefix-dynamical class, while retaining a one-word
radical and exact control of every classical finite-dimensional shadow.
