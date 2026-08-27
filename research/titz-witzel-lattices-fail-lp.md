---
rg: 2
id: titz-witzel-lattices-fail-lp
kind: claim
title: The full C*-algebras of the Titz-Witzel lattices and their simple subgroups fail the lifting property
distinct_from:
  compact-hyperbolic-km-lattices-fail-lp: that is the still-open LP fork for the NON-uniform Kac--Moody lattices, where every Brown-type shortcut is fenced off by non-cocompactness; this is the same statement PROVED for the uniform Titz-Witzel lattices, where the free cocompact action makes the shortcut a theorem.
  llp-non-rf-kazhdan-group-is-non-hyperlinear: that consumes LLP positively for non-RF Kazhdan groups; this is the unconditional negative LP statement for the sharpest such candidates, splitting the remaining question cleanly into LLP-versus-LP.
---

**THEOREM.**  Let `Gamma` be any of the five Titz Mite--Witzel uniform
`C~_2`-lattices, or any of their finite-index simple subgroups
`Gamma^`.  Then `C^*(Gamma)` does not have the (global) lifting property
LP.

These are the first LP failures for torsion-free simple groups, and the
first for building lattices whose obstruction does not pass through a
congruence or arithmetic pair: the input is property (T) plus
`H^2(Gamma, Z Gamma) != 0`, with the second cohomology carried by the
building's top-degree compactly supported cohomology.

**Consequence for the program.**  Combined with
`titz-witzel-simple-kazhdan-cat0-lattices-exist` and the fence exclusions
(`twin-lattices-exclude-known-llp-fences`, plus torsion-freeness and
simplicity), the LLP question for these groups is now the exact analogue
of the Kac--Moody fork with the LP side DECIDED: if `C^*(Gamma^)` has the
LLP then `Gamma^` is non-hyperlinear
(`llp-non-rf-kazhdan-group-is-non-hyperlinear`) — an explicit finitely
presented torsion-free simple witness — AND LLP is separated from LP for
group C*-algebras, resolving the open comparison quoted by
Ioana--Spaas--Wiersma from Ozawa; if it fails, these are LLP failures of
a new kind (no relative-(T) pair, no expanders, no finite-dimensional
representations of the simple subgroups).  Either way the class settles
published questions; the dichotomy is recorded as
`titz-witzel-lattice-is-non-hyperlinear-or-llp-failure`.
