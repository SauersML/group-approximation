---
rg: 2
id: titz-witzel-dichotomy-proof
kind: route
title: Instantiate the non-RF Kazhdan lifting corner and the fence exclusions at the Titz-Witzel lattices
target: titz-witzel-lattice-is-non-hyperlinear-or-llp-failure
requires:
  - titz-witzel-simple-kazhdan-cat0-lattices-exist
  - titz-witzel-lattices-fail-lp
  - llp-non-rf-kazhdan-group-is-non-hyperlinear
  - twin-lattices-exclude-known-llp-fences
  - non-rf-kazhdan-weak-ucp-iff-non-hyperlinear
---

`Gamma^` is finitely presented, Kazhdan, infinite simple, hence not
residually finite (`titz-witzel-simple-kazhdan-cat0-lattices-exist`).
If `Gamma^` is hyperlinear, then by
`non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` it is not weakly
ucp-stable, and by the contrapositive of
`llp-non-rf-kazhdan-group-is-non-hyperlinear` its full C*-algebra fails
the LLP; `titz-witzel-lattices-fail-lp` supplies the unconditional LP
failure in both cases.  If `Gamma^` is not hyperlinear it is the goal's
witness.  The exclusivity is definitional.  The "no published mechanism"
clause of case (b): scalar-image finite-dimensional projective
representations for infinite simple groups (Malcev, as recorded on
`non-rf-kazhdan-group-with-llp-full-c-star-algebra`), torsion-freeness
from the free action on the CAT(0) model, and parts (b)/(d) of
`twin-lattices-exclude-known-llp-fences` applied to the single-building
proper cocompact cellular action.
