---
rg: 2
id: property-t-free-torsion-free-via-embedding-router
kind: route
title: Embed the radical word into a group it normally generates, then upgrade to two generators
target: property-t-free-torsion-free-full-mf-radical
requires:
  - property-t-free-torsion-free-fp-non-mf-seed
  - universal-mf-quotient
  - torsion-free-embedding-normal-generation-router
  - two-generated-acylindrical-normal-generation-upgrade
  - mf-radical-saturation-along-any-homomorphism
---

1. Take a finitely presented torsion-free non-MF `E` from the seed.
   `universal-mf-quotient` gives `1!=d in Rad_MF(E)`.  Unlike
   `property-t-free-torsion-free-via-bs-radical-tether`, no acylindrical tether
   is needed, because the router input is not required to be acylindrically
   hyperbolic.
2. `torsion-free-embedding-normal-generation-router` gives
   `iota:E->P` with `P` finitely presented and torsion-free,
   `normalClosure_P(d)=P`, and `iota(d)!=1`.
3. `two-generated-acylindrical-normal-generation-upgrade` applied to `(P,d)`
   gives `g:P->Q` with `Q` two-generated, finitely presented,
   torsion-free and acylindrically hyperbolic, `g(d)!=1` and
   `normalClosure_Q(g(d))=Q`.
4. `mf-radical-saturation-along-any-homomorphism` applied to `g∘iota` gives
   `Rad_MF(Q)=Q` and full radical for every nontrivial quotient.

No step uses Property `(T)`.  Compared with the existing routes, the
normal-generation clause `(TFR3)` is now an established elementary lemma, and
the hole is narrowed to the two-generation/acylindrical passage.
