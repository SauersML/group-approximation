---
rg: 2
id: odd-maslov-llp-via-vanishing-defect-homogeneous-retract
kind: route
title: Scalarize a homogeneous odd-to-even retract by driving its coefficient boundary to zero
target: sp4-mod3-twisted-fibres-have-llp
requires:
  - odd-maslov-homogeneous-split-ucp-retract-is-impossible
---

**INVALIDATED, IN THE STRONGER EXACT SENSE.**  The proposed route was to
construct homogeneous split ucp maps from an odd Maslov fibre into matrix
amplifications of an even fibre, let the coefficient size grow, and make the
two-sided multiplicative defects tend to zero before perturbing to a finite
Morita bridge.

The uniform Folner-gap theorem already ruled out the vanishing-defect limit.
`odd-maslov-homogeneous-split-ucp-retract-is-impossible` now rules out the
entire exact homogeneous split-retract premise: multiplicative-domain
equality for the left inverse extracts a nonzero finite-dimensional
projective coefficient on the support of the canonical coefficient state,
with the forbidden odd difference multiplier.  This argument allows the
left inverse to be nonfaithful and makes no equivariance assumption on it.

Thus a macroscopic positive boundary hidden by the retraction does not save
exact homogeneity.  Any surviving retract proof of odd-fibre LLP must drop
exact matrix homogeneity itself; it cannot merely retain a larger hidden
boundary.
