---
rg: 2
id: bohr-residual-equals-finite-residual-for-profinite-targets-proof
kind: route
title: van Dantzig, plus finite index of an open subgroup of a compact group
target: bohr-residual-equals-finite-residual-for-profinite-targets
requires: []
artifacts:
  - GroupApproximation/Analysis/PeterWeylProfinite.lean
---

## Direct proof, machine-checked

**The easy inclusion.**  `CompactTarget.ofFinite` exhibits a finite group with
the discrete topology as a compact Hausdorff topological group; a homomorphism
onto a finite quotient is therefore one of the maps the Bohr residual
quantifies over, so `bohrResidual <= finiteResidual`.

**Separation in a profinite group.**  For `c != 1` in a compact totally
disconnected group, `{c}` complement is an open neighbourhood of `1`, and
Mathlib's van Dantzig -- `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`
-- produces an open normal subgroup `H` inside it, so `c` is not in `H`.  An
open subgroup of a compact group has finite index
(`Subgroup.quotient_finite_of_isOpen`, then
`Subgroup.finiteIndex_of_finite_quotient`).  That is
`exists_normal_finiteIndex_not_mem`: finite quotients separate the points of a
profinite group.

**The other inclusion.**  Given `f : G ->* C` with `C` profinite and `g` in the
finite residual, suppose `f g != 1`.  Separate it by a normal subgroup of
finite index, pull back along `f` (`finiteIndex_comap`), and `g` lies outside a
finite-index normal subgroup of `G` -- contradicting membership in the finite
residual.  So `finiteResidual <= ker f`, which is
`finiteResidual_le_ker_of_profinite`.

Combining the two gives the equality for profinite targets, with no hypothesis
anywhere.
