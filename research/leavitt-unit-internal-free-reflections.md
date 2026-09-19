---
rg: 2
id: leavitt-unit-internal-free-reflections
kind: claim
title: The binary Leavitt MF black hole internally realizes every finite-rank free MF reflection
root: true
artifacts:
  - research/leavitt-unit-internal-free-reflections-proof.md
---

Let `U=L_(F_2)(1,2)^x`.  For every integer `r>=2`, there is an explicit
embedding

```text
W_r=U^(F_r) semidirectProduct F_r = U wr F_r <= U,       (IF1)
```

where `F_r` acts regularly on its own coordinates.  The group `W_r` is
finitely generated and

```text
Rad_MF(W_r)=U^(F_r),          R_MF(W_r) ~= F_r.          (IF2)
```

Precomposition with the quotient `q_r:W_r->F_r` gives a natural bijection

```text
Hom(F_r,M) ~= Hom(W_r,M)                              (IF3)
```

for every MF group `M`.  The same factorization holds for finite groups,
residually finite groups, compact Hausdorff groups, and finite-dimensional
linear groups over every field.

For every normal subgroup `N` of `W_r`, the complete semantic closure is

```text
cl_MF^(W_r)(N)=q_r^(-1)(cl_MF^(F_r)(q_r(N))).            (IF4)
```

The radical `U^(F_r)` is normally generated in `W_r` by one fixed involution
in the identity coordinate.  Moreover,

```text
W_r/N is MF
 iff U^(F_r)<=N and F_r/q_r(N) is MF.                    (IF5)
```

Thus pullback along `q_r` identifies the lattice of MF-closed normal
subgroups of `F_r` with that of `W_r`.  In particular, if `S` is normal in
`F_r`, then

```text
W_r/q_r^(-1)(S) ~= F_r/S
```

is MF exactly when `S` is MF-closed in `F_r`.  Thus the quotient lattice of
one finitely generated subgroup of `U` internally contains the complete MF
closure problem for all `r`-generated groups.

The groups `W_r` are pairwise nonisomorphic because their universal MF
quotients are the free groups of distinct ranks.  Hence one fixed simple
finitely generated Kazhdan MF black hole contains infinitely many
pairwise-nonisomorphic finitely generated non-MF subgroups with nonamenable
MF reflections.
