---
rg: 2
id: bs12-s3-content-satisfies-generalized-kl
kind: claim
title: The binary-dilation two-variable content embeds every coefficient group
artifacts:
  - research/bs12-s3-content-satisfies-generalized-kl-proof.md
distinct_from:
  kervaire-laudenbach-nonsingular-conjecture: that is the open one-variable conjecture for every nonsingular content; this proves one explicit two-variable content by a six-sheet HNN reduction.
  kl-violating-equation-over-leavitt-unit-group: that asks for an equation killing a binary-Leavitt coefficient; this theorem globally fences a tempting multivariable candidate before any Leavitt specialization.
---

For every group `G` and every five coefficients `g0,...,g4 in G`, the
natural map from `G` to

```text
<G,t,s | g0 t g1 s g2 t^(-1) g3 s^(-1) g4 t=1>
```

is injective.  Thus the content

```text
q=[t,s]t=t s t^(-1) s^(-1) t
```

cannot furnish a generalized Kervaire--Laudenbach counterexample over the
binary Leavitt unit or elementary group.

The content relation is `s t s^(-1)=t^2`, so its content group is
`BS(1,2)`.  Its quotient with `t=(123)` and `s=(12)` is `S3`; the kernel is
the binary-dilation subgroup `BS(1,4)`.  Reidemeister--Schreier rewriting of
the coefficient-deformed relation over this regular six-sheet cover, followed
by exact Tietze elimination, leaves

```text
p L(x) p^(-1)=R(x)
```

over `(*_(S3) G)*<x>`, with `x`-exponent sums `-1` in `L` and `-4` in
`R`.  Both associated elements have infinite order, so this is an ordinary
HNN extension between infinite cyclic subgroups.  Britton's lemma embeds the
entire free product of the six coefficient copies, and in particular the
original copy of `G`.
