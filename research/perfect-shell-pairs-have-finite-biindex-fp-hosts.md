---
rg: 2
id: perfect-shell-pairs-have-finite-biindex-fp-hosts
kind: claim
title: Perfect decidable inputs admit a shell stabilizer of finite bi-index in a finitely presented overgroup
distinct_from:
  perfect-decidable-inputs-have-fp-shell-envelopes: that requires E_nu itself to be finitely presented; this permits a larger finitely presented group but keeps the exact shell point stabilizer and asks for its finite bi-index there.
artifacts:
  - research/artifacts/boone-higman-spatial-overgroup-and-coset-gate-2026-09-08.md
---

For every infinite perfect finitely presented group P with decidable
word problem, there exist an enumeration nu and an abstract embedding
E_nu<=Gamma in a finitely presented group such that H=(E_nu)_p has
finite bi-index in Gamma. This is OPEN.

The older finitely presented shell-envelope hypothesis would imply
this by taking Gamma=E_nu, where H has exactly two double cosets.
The present statement allows E_nu not to be finitely presented.

Finitely presented overgroups of some computable decidable E_nu
already exist by Clapham. What is missing is control of the exact
subgroup H inside one of those overgroups. The intersection theorem
forces E_nu to meet every conjugate of itself infinitely; a proper
malnormal Higman embedding cannot close the claim.

Computability of a successful nu follows automatically: E_nu is
a finitely generated subgroup of a finitely presented group, hence
recursively presented, and the existing shell extraction theorem
computes nu from such a correctly marked presentation.
