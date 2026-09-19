---
rg: 2
id: torsion-free-non-mf-from-defect-saturation
kind: route
title: A group whose MF radical is everything is itself non-MF
target: torsion-free-finitely-presented-non-mf
requires: [defect-saturation-full-mf-radical]
artifacts:
  - GroupApproximation/Sofic/DefectSaturation.lean
  - notes/COMPRESSION_COLLAPSE_MF_RADICAL.md
---

## Why sufficient

[[defect-saturation-full-mf-radical]] asserts a two-generated finitely
presented torsion-free property-(T) acylindrically hyperbolic `G` whose
compression defect is all of `G`, so that `Rad_MF(G) = G`.  The last step to
this root is the cheap one: `Rad_MF(G) = G` says every homomorphism from `G`
into an MF group is trivial.  Were `G` itself MF, the identity would be a
nontrivial homomorphism from `G` into an MF group, forcing `Rad_MF(G) = 1`;
and `G != 1` because a two-generated Kazhdan acylindrically hyperbolic group
is nontrivial.  So `G` is not MF, while being torsion-free and finitely
presented by construction.

The route therefore consumes only three of the source claim's adjectives —
torsion-free, finitely presented, full radical.  Property (T) and acylindrical
hyperbolicity are how the source is *built*; this root does not ask for them,
and nothing downstream of this route may assume them.

## Why it is recorded even though the root is already established

The root is closed by `torsion-free-non-mf-from-normal-kazhdan-defect`, whose
existence input is Fournier-Facio's published skeleton.  This route reaches the
same statement from the saturation architecture instead, and it is strictly
stronger where it lands: it yields not just one non-MF group but one all of
whose nontrivial quotients are non-MF.  Recording it keeps the saturation lane
attached to a root, so that closing
[[defect-saturation-full-mf-radical]] visibly pays into the program rather than
into a detached corner.

The existence input it still owes is a Hull/Osin small-cancellation
formalization; the elementary substitute for that input is
[[bespoke-routing-lemma]], routed separately by
`torsion-free-non-mf-from-bespoke-router`.
