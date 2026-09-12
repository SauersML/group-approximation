---
rg: 2
id: internal-mf-reflections-have-a-finite-expression-calculus
kind: claim
title: Virtually free reflections generate an internal finite product-wreath calculus
root: true
artifacts:
  - research/internal-mf-reflections-have-a-finite-expression-calculus-proof.md
---

Let `C` be the smallest class of countable groups such that

1. every countable virtually free group belongs to `C`;
2. every finite direct product of groups in `C` belongs to `C`;
3. if `Q` belongs to `C` and `F` is finite, then `Q wr F` belongs to `C`.

For every `Q in C`, the one binary Leavitt unit group `U` contains a subgroup
`K_Q` and a split quotient `pi_Q:K_Q->>Q` such that

```text
Rad_MF(K_Q)=ker(pi_Q),                 R_MF(K_Q)~=Q,     (FEC1)
Hom(Q,M)~=Hom(K_Q,M)                                  (FEC2)
```

naturally for every MF group `M`.  For every normal subgroup `N` of `K_Q`,

```text
cl_MF^(K_Q)(N)=pi_Q^(-1)(cl_MF^Q(pi_Q(N))),             (FEC3)

K_Q/N is MF
 iff ker(pi_Q)<=N and Q/pi_Q(N) is MF.                  (FEC4)
```

Every group in `C` is residually finite.  Consequently the MF, finite,
compact, finite-dimensional unitary, and linear residual over every field of
`K_Q` all equal `ker(pi_Q)`, and

```text
profiniteCompletion(K_Q)~=profiniteCompletion(Q),
Bohr(K_Q)~=Bohr(Q).                                     (FEC5)
```

If `Q` is described by a finite expression whose virtually free leaves are
finitely generated, then `K_Q` is finitely generated.  Its radical has a
finite normal generating set: product nodes add the numbers of normal
generators, while a transitive wreath node preserves the number for
isomorphic branches.

Thus one fixed simple finitely generated Kazhdan MF black hole internally
realizes a recursively closed class of residually finite MF reflections far
beyond the context-free groups, with exact control of every quotient closure
and every classical finite-dimensional shadow.
