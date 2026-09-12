---
rg: 2
id: mf-invisible-classical-completions-proof
kind: route
title: Compare the camouflage group with its free quotient through every completion
target: mf-is-invisible-to-classical-representation-completions
requires:
  - non-mf-groups-with-free-integral-representation-geometry
  - finite-residual-quotients-are-universal-linear-reflections
---

Use the groups `Gamma_r=C_d(F_r)` and their split quotient maps from the free
representation-geometry theorem.  Free groups are MF, while the camouflage
kernel contains the nonidentity element `d` and is killed by every MF-target
map; hence `Gamma_r` is non-MF.

Every finite quotient of `Gamma_r` factors uniquely through `F_r`, so the
finite-residual reflection theorem gives the profinite isomorphism and the
equivalence on finitely presented module representations.  Its specialization
to finite-dimensional vector spaces, together with preservation of tensor
products and the forgetful functor, gives the Tannakian and proalgebraic
statements.  The integral representation-geometry theorem supplies the
scheme, stack, character-quotient, and deformation identifications.

Every map from the hidden vertex group to a compact group is trivial:
Peter--Weyl point separation would otherwise produce a nontrivial
finite-dimensional unitary representation.  The amalgam factorization then
identifies all maps from `Gamma_r` to compact groups with those from `F_r`.
Their Bohr compactifications are therefore isomorphic.

For `r=0`, `F_0=1`.  All the universal completions are consequently trivial,
and the integral representation scheme is `GL_n^0=Spec(Z)`.  The full module
statement is the equivalence

```text
Rep_A^fp(Gamma_0) ~= Mod_A^fp,
```

whose right side regards every finitely presented module as carrying the
trivial action.  The element `d` remains nonidentity by amalgam normal form,
so `Gamma_0` itself is nontrivial and non-MF.
