---
rg: 2
id: monomial-hnn-wreath-sofic-non-mf-proof
kind: route
title: Combine monomial action soficity with GKP wreath permanence and the involutive HNN collapse
target: monomial-hnn-wreath-sofic-non-mf
requires:
  - monomial-ascending-hnn-coset-action-sofic
  - gkp-sofic-action-toolkit
  - hnn-one-site-lamp-is-a-torsion-compression-witness
  - involutive-compression-collapse
artifacts:
  - research/artifacts/ascending-hnn-iterated-coset-solution-2026-08-18.md
  - GroupApproximation/Sofic/AscendingHNNWreathWitness.lean
---

## Sofic half

`Gamma=EL_r(F_q[x_1,...,x_d])` is residually finite, hence sofic.  The
ascending telescope kernel is a directed union of copies of `Gamma`, hence
sofic, and adjoining the stable-letter quotient `Z` preserves soficity.  The
prerequisite `monomial-ascending-hnn-coset-action-sofic` supplies a sofic
action on `V_A/Gamma`.  The finite lamp `C_2` is sofic, so the GKP generalized
wreath theorem gives soficity of `W_A`.

## Non-MF half

For a proper self-embedding choose `a` outside the image.  The one-site
nontrivial `C_2` lamp at `t Gamma` is an involutive compression witness; its
commutator with `a` is nontrivial.  The established involutive compression
collapse puts that nontrivial commutator in the MF residual.  Hence `W_A` is
not MF.
