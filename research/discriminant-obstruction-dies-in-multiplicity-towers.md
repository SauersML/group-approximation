---
rg: 2
id: discriminant-obstruction-dies-in-multiplicity-towers
kind: claim
title: The discriminant obstruction to full square-zero elements dies along unital multiplicity towers
invalidates: [homogeneous-tower-via-discriminant-obstruction]
distinct_from:
  full-square-zero-forces-discriminant-power-vanishing: that proves the obstruction for one bundle; this shows it cannot hold at infinitely many stages of a diagonal tower with unbounded rank, so it cannot produce a limit counterexample.
---

**ESTABLISHED (obstruction to a route).**  Let `A_j=Gamma(X_j, End E_j)` be
homogeneous algebras over compact Hausdorff spaces with `rank E_j=N_j -> infinity`.
Suppose each connecting map `phi_j:A_j->A_(j+1)` has **multiplicity form**:

```text
E_(j+1) ~= directSum_(i=1)^(m_j)  lambda_(j,i)^* E_j  tensor  V_(j,i),
phi_j(f) = directSum_i  lambda_(j,i)^*(f) tensor 1,
```

for continuous `lambda_(j,i):X_(j+1)->X_j` and vector bundles `V_(j,i)` of
rank at least one.  This covers the diagonal constructions of Goodearl,
Villadsen and Toms, point evaluations included (constant `lambda`).

Then `Delta(E_j)^(floor(N_j/2))=0` for every sufficiently large `j`.  So along
such a tower the obstruction of
`full-square-zero-forces-discriminant-power-vanishing` excludes full
square-zero elements at only finitely many stages.  By
`unital-limit-full-square-zero-at-finite-stage` a unital limit counterexample
needs an obstruction at **every** stage, so the discriminant alone cannot
supply one.

It does not cover twisted connecting maps whose spectrum map
`X_(j+1) -> Sym^k(X_j)` does not lift to `X_j^k`, and it says nothing about
other characteristic obstructions.
