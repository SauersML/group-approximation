---
rg: 2
id: leavitt-unit-internal-mf-reflection-tower
kind: claim
title: One simple MF black hole contains an infinite tower of iterated-wreath MF reflections
root: true
artifacts:
  - research/leavitt-unit-internal-mf-reflection-tower-proof.md
---

Let `U=L_(F_2)(1,2)^x`, and let `F` be a nontrivial finite group.  There are
sequences of finitely generated groups `K_m<=U` and finitely generated
amenable groups `Q_m` defined by

```text
K_0=U wr F,                    Q_0=F,
K_(m+1)=K_m wr Z,              Q_(m+1)=Q_m wr Z.          (IRT1)
```

For every `m>=0`, there is a canonical epimorphism `pi_m:K_m->Q_m` such that

```text
Rad_MF(K_m)=ker(pi_m),          R_MF(K_m) ~= Q_m.         (IRT2)
```

Precomposition with `pi_m` is a natural bijection

```text
Hom(Q_m,M) ~= Hom(K_m,M)                               (IRT3)
```

for every MF group `M`.

One nonidentity involution `d` in the original copy of `U` normally
generates every `ker(pi_m)`.  For every normal subgroup `N` of `K_m`,

```text
cl_MF^(K_m)(N)=N normalClosure_(K_m)(d),                 (IRT4)
K_m/N is MF  iff  d belongs to N.                        (IRT5)
```

Thus one fixed word controls the complete MF quotient theory at every level.
All the groups `K_m` are non-MF subgroups of the same simple finitely
generated Kazhdan group `U`, while their MF reflections form an unbounded
elementary-amenable complexity tower.  For `F=C_2`, the group `Q_m` has
derived length exactly `m+1`, so the `K_m` are pairwise nonisomorphic.
