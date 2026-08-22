---
rg: 2
id: leavitt-degree-kernel-quotient-tests-are-procyclic
kind: claim
title: Every finite or solvable quotient test of a Leavitt degree kernel is cyclic and sees every degree-m word as a generator
distinct_from:
  degree-kernel-abelianization-is-infinite-cyclic: That computes only the first homology of the degree kernel for an arbitrary perfect coefficient group; this controls every finite and solvable quotient using the stronger fact that the Leavitt unit group has no finite quotients.
  perfect-two-generator-relation-module-not-cyclic: That obstructs one-relator presentations of perfect quotients of free groups; this concerns the degree kernel inside a free product with a cyclic group, where the abelianized relation-module test is vacuous.
  uniform-normal-rank-certificate-for-degree-kernels: That asks for a certificate proving no single word normally generates a degree kernel; this proves that no such certificate can live in a finite or solvable quotient for the Leavitt coefficient group.
  leavitt-degree-kernel-normally-generated-by-one-word: That asks for a positive normal-generation identity; this identifies the exact kind of infinite perfect quotient that would have to witness failure, without deciding whether such a quotient exists.
---

Let `G=L_(F_2)(1,2)^x`, let `m>=1`, and put

```text
F=G*<t>,        N_m=ker(F -> C_m).
```

Then:

1. every homomorphism from `N_m` to a finite group has cyclic image and
   factors through `deg_t/m:N_m->Z`; hence the profinite completion of `N_m`
   is canonically the procyclic group `Zhat`;
2. every homomorphism from `N_m` to a solvable group has cyclic image and
   factors through the same map;
3. if `w in N_m` has `deg_t(w)=m`, its image generates every such cyclic
   image.

In particular, if

```text
L_w=<<w>>_F <= N_m,       Q_w=N_m/L_w,
```

then `Q_w` is perfect and has no nontrivial finite or solvable quotient.  Thus
either `Q_w=1` (the desired Kervaire--Laudenbach violation) or the obstruction
to normal generation is an **infinite perfect group with no finite
quotients**.  Finite quotient enumeration, nilpotent quotients, derived
quotients, and all other solvable relation-module tests are provably blind to
the distinction.

