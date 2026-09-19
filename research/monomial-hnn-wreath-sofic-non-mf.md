---
rg: 2
id: monomial-hnn-wreath-sofic-non-mf
kind: claim
title: Proper monomial Kazhdan HNN wreath products are sofic and non-MF, including infinite-index compressors
distinct_from:
  positive-core-bernoulli-ce: That concerns the positive core and Connes embeddability; this is a full HNN permutational wreath product with simultaneous soficity and failure of MF.
  hnn-one-site-lamp-is-a-torsion-compression-witness: That is the structural non-MF witness valid for arbitrary HNN data; this claim combines that existing negative mechanism with the new monomial action-soficity theorem to get a positive/negative approximation separation.
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
  - GroupApproximation/Sofic/AscendingHNNWreathWitness.lean
---

In the setting of [[monomial-ascending-hnn-coset-action-sofic]], assume the
monomial self-embedding is proper and use the lamp `C_2`.  Then

`W_A = (direct_sum_{V_A/Gamma} C_2) semidirect V_A`

is **sofic and non-MF**.

The base elementary polynomial group is residually finite/sofic and has
property (T); the telescope is a directed union of copies of it, and the HNN
group is a sofic-by-amenable extension by `Z`.  The new theorem gives a sofic
coset action, so GKP's generalized-wreath permanence theorem makes `W_A`
sofic.  Properness plus the involutive one-site lamp triggers the already
formalized HNN compression-collapse theorem, producing a nontrivial element
of the MF residual.  No finite-index-image assumption is needed.
