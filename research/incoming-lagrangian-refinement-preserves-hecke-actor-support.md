---
rg: 2
id: incoming-lagrangian-refinement-preserves-hecke-actor-support
kind: claim
title: Incoming-Lagrangian refinement preserves the wrong Hecke actor support
artifacts:
  - research/incoming-lagrangian-hecke-support-proof.md
distinct_from:
  fano-semidir-bridges-are-wrong-subgroup-or-gauged: that separates pure coefficient and actor words on the unrefined signed Hecke cut; this checks the proposed refinement by a Singer-normalized incoming-root Lagrangian and identifies exactly what a dual Pauli translation can change.
  heisenberg-subgroup-cuts-are-affine-stabilizer-flats: that classifies the available Pauli subgroup cuts; this tracks their support after multiplication by the signed Hecke Reynolds idempotent.
  el20-six-moving-coefficient-square-bridges: that still permits coefficient-sensitive words outside the finite Fano semidirect packet; this rules out only the proposed incoming-Lagrangian/dual-translation construction of those bridges.
---

**ESTABLISHED REFINED-PAULI FENCE.**  Let `A` be either the incoming or
dual seven-pair Pauli Lagrangian in the marked Fano packet and let `K` be
its binary actor group.  The Singer head `t=t_i` normalizes `A`.  Put

```text
H_k=t^kL_0t^(-k),          lambda_k=lambda_0 o Ad(t^(-k)),
Q_k=e_(H_k,lambda_k).                                  (ILR1)
```

Let `p_k` be any nonzero affine stabilizer idempotent in `C[A]` for which
`p_kQ_k=Q_kp_k`; this commutation is necessary for the proposed
Lagrangian refinement `F_k=p_kQ_k` to be a projection.  In the unique
normal form of the finite semidirect packet `A semidirect K`, every actor
quotient in the Fourier support of `F_k` lies in `H_k`, and every element
of `H_k` occurs.  Thus the actor-quotient support of `F_k` is exactly

```text
supp_K(F_k)=H_k.                                       (ILR2)
```

Conjugation by a dual Heisenberg/Pauli translation `a in A` preserves the
actor quotient:

```text
supp_K(aF_ka^(-1))=H_k.                                (ILR3)
```

It may multiply the coefficient of an actor `h` by the commutator phase
of `a` with `h`, hence change the character/cocycle on the **same**
subgroup.  It cannot replace `H_k` by `H_(k+1)`.

The difference between consecutive subgroups is genuine.  For the first
Singer row, in the actor basis `(2,4,5,6,7,8,9)`,

```text
d=I+e_2e_8^* in L_0,
t d t^(-1)=I+e_2e_7^* notin L_0,                       (ILR4)
```

because every generator of `L_0` fixes `e_7`, while the last transvection
does not.  Conjugating `(ILR4)` by `t^k` gives the corresponding mismatch
at every stage at which the two Singer translates differ.  Therefore no
pure Pauli translation can have both full Grams

```text
R_k^*R_k=F_k,             R_kR_k^*=F_(k+1).            (ILR5)
```

The same conclusion holds after refining by the whole Singer-normalized
incoming-root Lagrangian, by one of its affine flats, or by the dual
Lagrangian.  The refinement changes the `A`-coordinate support but not the
`K`-coordinate support in `(ILR2)`.

Hence the answer to the subgroup-versus-character question is exact:
`t` changes the Hecke **subgroup** from `L_0` to `tL_0t^(-1)` and transports
its character with it; a dual Pauli translation changes at most the
character/cocycle on `L_0`.  The six bridges, if they exist, must use
full-EL20 coefficient relations outside this refined finite semidirect
construction.  No Property `(T)`, Kazhdan input, or literature theorem is
used.

DERIVATION
incoming-lagrangian-hecke-support-proof
