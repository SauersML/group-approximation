---
rg: 2
id: restricted-burnside-finiteness
kind: claim
title: The restricted Burnside group R(m,N) is finite
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

**Literature input.**  For all `m, N >= 2` there are, up to isomorphism, only
finitely many finite `m`-generated groups of exponent dividing `N`.
Equivalently the **restricted Burnside group**

```text
R(m,N) = B(m,N) / (intersection of the finite-index normal subgroups)
```

is finite, where `B(m,N) = F_m / <<w^N : w in F_m>>` is the free Burnside
group. `R(m,N)` is therefore the largest finite `m`-generated group of
exponent dividing `N`, and **every** finite `m`-generated group of exponent
dividing `N` is a quotient of it.

Being finite, `R(m,N)` is finitely presented; fix once and for all a finite
presentation

```text
R(m,N) = < x_1,...,x_m | s_1,...,s_k >.                          (RB1)
```

The relators `s_j` are the **finite-residual relators**: when `B(m,N)` is
infinite they are consequences of the exponent law only in the sense of
finite-quotient validity, not as abstract group identities.

**Trust surface.**  This is the positive solution of the restricted Burnside
problem: Zelmanov, for prime-power exponent and then in general, reducing to
the classification of finite simple groups through the Hall--Higman theory.
It is a settled, refereed, textbook theorem, cited here and not reproved.
`R(m,N)` is not effectively computable in practice for most `(m,N)`, but
finiteness is all that is used downstream.
