---
rg: 2
id: literal-mark-quotient-finite-residual
kind: claim
title: Exact finite residual of the literal marked quotient
distinct_from:
  commuting-lamp-quotient-finite-residual: Same mechanism, different group and different answer: there the finite residual is a locally finite elementary abelian 2-group and the level-collapse quotient is a lamplighter; here it contains infinite-order elements and the level-collapse quotient is a free lamplighter.
  marked-quotients-not-lef: That claim rules out exact finite models qualitatively; this one computes the finite residual exactly.
  literal-telescope-split-normal-form: That claim is the algebraic splitting of `E`; this one computes an approximation-theoretic invariant of `E/<w>`.
  literal-mark-quotient-sofic: That claim builds permutation microstates for the same group; this one computes which of its elements no finite quotient can see, and the two combine to refute permutation stability.
  literal-mark-quotient-mf: That open claim is about operator-norm corona models; this proved claim computes finite quotients, which by themselves decide nothing about MF.
  literal-mark-quotient-flexibly-stable: That open claim is about permutation almost-actions and flexible enlargement; this proved claim is about honest homomorphisms to finite groups, and it settles the residual-finiteness disjunct appearing in that claim's status note.
artifacts:
  - notes/COMMUTING_LAMP_QUOTIENT_STRUCTURE_AND_MF_FORK_2026-08-14.md
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

Every homomorphism from `E/<w>` to a finite group gives all lamps of a
common telescope level the same image.  The finite residual of `E/<w>` is
exactly

```text
R = normal closure of { c_x c_{x'} : level(x) = level(x') } ,
```

and the level-collapse quotient is

```text
(E/<w>) / R  =  ( *_{n in Z} Z/2 ) semidirect V ,
```

with `V` acting through `level : V -> Z`; that group is residually finite,
hence LEF, hence MF.

`R` is not locally finite: two same-level lamps in different blocks generate
an infinite dihedral group whose generator product lies in `R`.  This is the
one structural asymmetry with the commuting-lamp quotient, where the
corresponding subgroup is elementary abelian.
