---
rg: 2
id: stw84-wreath-quotient-obstruction-proof
kind: route
title: Push the wreath-product dichotomy through group C*-quotients
target: stw84-wreath-quotient-obstruction
requires: []
---

Write `W=K wr H`.  Eckhardt--Wu's wreath-product dichotomy
([*Nuclear dimension and virtually polycyclic groups*, Theorem
C](https://doi.org/10.1016/j.aim.2025.110768)) says, for `K` virtually
polycyclic and `H` finitely generated virtually nilpotent, that

```text
dim_nuc(C*(K wr H))<infinity
    if and only if
K is finite or H is finite.
```

Thus the hypotheses in the claim give `dim_nuc(C*(W))=infinity`.  A group
epimorphism `G->W` induces a surjective *-homomorphism of full group
C*-algebras

```text
C*(G) -> C*(W).
```

Nuclear dimension does not increase on quotients.  Hence finite nuclear
dimension of `C*(G)` would imply finite nuclear dimension of `C*(W)`, a
contradiction.  (Amenability identifies these full algebras with the reduced
group algebras used in Problem LXXXIV.)

For completeness, the abelianization of a restricted wreath product is

```text
(K wr H)_ab = K_ab direct_sum H_ab.                 (1)
```

Indeed, after abelianizing the base, it becomes `direct_sum_H K_ab`.
Commutators with `H` impose the coinvariant relations identifying all
coordinates of this regular `H`-module.  Its coinvariants are `K_ab`, via the
finite-support coordinate-sum map.  The splitting `H->K wr H` supplies the
second summand in (1).

Now take `K=H=D_infinity`.  The infinite dihedral group is infinite,
finitely generated, virtually cyclic, and amenable, while

```text
(D_infinity)_ab = Z/2 direct_sum Z/2.
```

Both factors therefore meet Eckhardt--Wu's hypotheses, and (1) gives
`(D_infinity wr D_infinity)_ab=(Z/2)^4`.  This proves simultaneously that the
example is invisible to `stw84-abelianization-rank-lower-bound` and that the
new quotient obstruction is genuinely stronger than that lower mechanism.
