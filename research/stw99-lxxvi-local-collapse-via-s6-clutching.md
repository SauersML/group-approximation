---
rg: 2
id: stw99-lxxvi-local-collapse-via-s6-clutching
kind: route
title: Turn the unstable rank-two bundle over S6 into the ideal-local projection pair
target: stw99-lxxvi-ideal-local-collapse-witness
requires:
  - stw99-lxxvi-s6-clutching-collapse-witness
---

Let `D` satisfy the witness and put `A=C(S^6) tensor D`.  By Seth--Vilalta's
continuous-function theorem, `A` is pure.  Clutching the trivial
rank-two modules over the two hemispheres by `alpha` gives a projection `p`
over `A`; let `q` be the trivial rank-two projection.  Both projections are
full because every fiber has rank two and `D` is simple, so their generated
ideal is all of `A tensor K`.

The class `alpha` is stably zero: its stabilization from `pi_5(U(2))=Z/2`
lands in the torsion-free stable group `pi_5(U)=Z`, hence vanishes.  Therefore
`[p]=[q]` in `K_0(A)`.  Condition 1 says the two `D`-module bundles are not
isomorphic, so their projection classes in `Cu(A)` are distinct.  Condition 2
makes the clutching maps homotopic after tensoring with Z, so
`p tensor 1_Z` and `q tensor 1_Z` are Murray--von Neumann equivalent.  This is
the required ideal-local collapse witness.
