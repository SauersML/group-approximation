---
rg: 2
id: fournier-facio-hnn-single-shadow-bug-proof
kind: route
title: Britton preserves the commutator and Kazhdan transport erases its HS shadow
target: fournier-facio-hnn-single-shadow-bug
requires:
  - fournier-facio-torsion-free-skeleton
  - kazhdan-asymptotic-commutant-transport
artifacts:
  - research/artifacts/shadow-kleene-saturation-compiler-2026-08-22.md
  - GroupApproximation/Sofic/OpToHSShadowResidual.lean
---

The direct-product relation `[S,P_1]=1` gives `[u_1^-1 s u_1,P]=1`, and
transport by `u_1` recovers `s`.  Property (T) makes this one-sided
centralizer transport valid in every normalized-HS ultraproduct shadow of an
operator-norm almost representation, so `[s,x]` dies for `x in S<=P`.
Nonabelian simplicity supplies `s,x` with nontrivial commutator, and Britton's
lemma embeds `P` into the HNN extension.  The checked declarations are
`witness_commutator_mem_opToHSShadowResidual` and
`exists_nontrivial_opToHSShadowBug`.
