---
rg: 2
id: lcs-anchor-shared-pauli-splitters-have-k4-model
kind: claim
title: Globally shared Pauli outcome gates and exact marginal products admit a K4 cheating model
artifacts:
  - research/artifacts/lcs-anchored-attack-2026-09-20.md
distinct_from:
  row-glued-magic-squares-absorb-noncommuting-ports: That glues private gadgets through a port-independent row; this shares every outcome gate across vertex and edge contexts and satisfies all fine-to-coarse marginal products.
  controlled-pauli-commutator-robustly-measures-projection-overlap: That provides the decoder after literal controlled form is established; this disproves one concrete attempt to force that form using globally shared gates, normalization, and marginals.
  lcs-pc-zero-noise-coloring-cheat: That gives scalar characters for the unmodified TV test; this gives a non-scalar shared Pauli representation of a changed controlled-gate test.
  central-character-profiles-affine-under-odd-tensor-products: That is an atomwise scalar-port closure theorem; this verifies an explicit global representation through overlapping vertex and edge measurement contexts.
---

Consider the candidate presentation in Sections 2--4 of the artifact:
one Pauli anchor X,Z,J; one globally shared U_t,V_t,s_t per source
projection atom; covariance and same-atom commutator identities (2);
PVM-context normalization and orthogonal cross-commutation (3); and
both U and V fine-to-coarse marginal product identities (4).

Every exact source projection model extends by literal controlled
Pauli gates. Nevertheless, on the K4 three-colouring projection source
this presentation has an exact 2^15-dimensional representation with
J=-I and s_(i,a)=-I for every vertex and all three colours. Thus its
decoded source atoms (1-s_(i,a))/2 are all I and do not form a PVM.

The model also satisfies the full local subset/AND commutator table
(19), not just single-atom relations. It extends to every u-fold product
source in dimension 2^(15^u), although the repeated source's unrestricted
quantum value tends to zero.

The precise escape is a nonzero isotropic atom vector: s_t=I but U_t!=I.
An outcome with decoded projection zero can still carry a nontrivial
gate that enforces global marginal identities. Thus shared covariance,
normalization and marginal products do not authenticate literal
controlled form, and this particular candidate has no generic positive
source decoder. No impossibility of all anchored LCS compilers is asserted.
