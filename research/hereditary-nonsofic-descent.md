---
rg: 2
id: hereditary-nonsofic-descent
kind: claim
title: Nonsoficity descends abstractly to every nontrivial quotient of the routed group
distinct_from:
  nonsofic-hyperbolic-group: That claim asserts nonsoficity of one specific (acylindrically) hyperbolic group; this one is the abstract descent statement that EVERY nontrivial quotient of the routed full-radical group inherits nonsoficity, via simple-subgroup survival, independent of any hyperbolicity.
artifacts:
  - GroupApproximation/Sofic/HereditaryNonsoficDescent.lean
---

Abstract descent for the Fournier--Facio routed quotient, with no small
cancellation and no geometry.  Three graded statements.

1. **Exactness** (no hypotheses): the hidden compression defect of a
   Fournier--Facio datum equals the normal closure of the embedded
   simple factor, `defectNormal = normalClosure(S)`.

2. **Survival** (no hypotheses beyond the routing datum): in every
   nontrivial quotient `H` of the routed group `Q`, the simple factor
   `S` injects.  Killing `S` kills its normal closure, hence by
   exactness the whole defect, whose image is all of `Q` — so `H`
   would be trivial.  Consequently, if `S` is itself nonsofic, EVERY
   nontrivial quotient of `Q` is nonsofic, since soficity passes to
   subgroups.

3. **Criterion descent** (interface-gated): the Fournier--Facio
   nonsoficity criterion's `CompressionSetup` descends along any
   surjection except for exactly two injectivity constraints — the
   Kazhdan copy staying injective and the compressed copy staying
   disjoint from the commuting copy.  Given retention of those two
   constraints in every nontrivial quotient, every nontrivial quotient
   of `Q` is nonsofic, and the combined hereditary package (full
   corona MF radical, non-MF in both conventions, nonsofic) holds for
   each of them.

The residual trusted boundary for the one-paper program's hereditary
headline is therefore exactly: retention of two injectivity
constraints through the small-cancellation quotient, or alternatively
nonsoficity of the simple factor itself.  Related gate:
`bespoke-routing-lemma`.
