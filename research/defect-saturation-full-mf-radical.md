---
rg: 2
id: defect-saturation-full-mf-radical
kind: claim
title: Defect saturation gives groups with full MF radical
artifacts:
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
  - GroupApproximation/Sofic/DefectSaturation.lean
---

Credit: the small-cancellation route is Fournier-Facio's suggestion
(personal communication 2026-08-14, "analogously to what I do in
arXiv:2608.02025"); the saturation/full-radical framing is a session
development of that idea (GPT-5.6-assisted), unrefereed.

Claim: there is a 2-generated finitely presented torsion-free
property-(T) acylindrically hyperbolic group G whose compression defect
is all of G, so that (by the in-repo normalKazhdan_le_normMFResidual)
Rad_MF(G) = G: every homomorphism to an MF group is trivial and every
nontrivial quotient is non-MF.  Route: FF's arXiv:2608.02025 compression
configuration + a Hull Theorem 7.1 quotient making the surviving simple
subgroup normally generate.  The Lean plumbing (saturation implies full
radical, black-hole quotient triviality, non-MF-ness) is now
machine-checked unconditionally in
GroupApproximation/Sofic/DefectSaturation.lean; the existence input
still needs a Hull/Osin small-cancellation formalization program.
