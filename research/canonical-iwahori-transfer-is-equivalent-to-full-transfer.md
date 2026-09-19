---
rg: 2
id: canonical-iwahori-transfer-is-equivalent-to-full-transfer
kind: claim
title: Canonical Iwahori projection transfer is equivalent to the full unitary transfer modulus
distinct_from:
  iwahori-transfer-equals-matricial-commutant-codensity: that identifies full transfer with a relative-commutant equality for every matrix-ultraproduct representation; this proves restricting to the canonical character does not shrink the class of possible failures.
---

The sequential claim `canonical-iwahori-projection-commutant-transfer` holds
if and only if the dimension-free modulus in
`iwahori-unitary-commutant-transfer` exists.

One direction is immediate: full unitary transfer applies to canonical
sequences, and the selfadjoint-unitary/projection conversion loses only a
fixed factor.

Conversely, if the full modulus failed, then
`iwahori-transfer-failure-reduces-to-two-block-projection` would give a
failed projection sequence, with positive-density blocks by
`iwahori-transfer-failure-has-two-positive-density-blocks`.
`residual-finite-tensor-camouflages-iwahori-transfer-failures` tensors that
sequence with finite-quotient regular representations and makes its full
amalgam character canonical without changing any defect or failed
commutator.  This contradicts canonical projection transfer.

Therefore canonical character tests are valuable for selecting finite local
types, but they do not make this terminal relative-commutant theorem easier:
arbitrary failures can be hidden behind a regular tensor at zero normalized-
HS cost.

The same equivalence persists after adding moving root-polynomial tests.
`regular-tensor-camouflage-preserves-moving-root-failures` observes that if
`N_n` is the quotient order of a root, then its `N_n`-th power in the tensor
amplification is the payload root power tensored with identity. Thus the
regular factor cannot enforce the moving-coefficient opposite-root
orthogonality enjoyed by a pure regular packet. Any proof using that
orthogonality must first establish full relative congruence capture.
