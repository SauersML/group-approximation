---
rg: 2
id: per-compressor-component-matching-proof
kind: route
title: Change the distinguished compressor of the local criterion data and reuse the landed matching preparation
target: per-compressor-component-matching-over-shared-decompositions
requires: []
artifacts:
  - GroupApproximation/KunThom/CompressorMatching.lean
---

Proved in Lean, `GroupApproximation/KunThom/CompressorMatching.lean`, landed
773d7952c with probe 0912-131855-83868 green.

1. **Same decompositions.**
   - The Γ-decomposition depends on the setup only through `embedΓ` and `generatorsΓ`.
   - The ambient decomposition depends on it only through
     `ambientGenerators = S ∪ Q ∪ Q⁻¹`.
   - Neither mentions the distinguished compressor. So
     `LocalCriterionData.withDistinguished` takes both fields by definitional
     unfolding, with no cast.
   - For a trivial commuting factor, `centralizes` and `disjoint` hold for any
     compressor: `embedJ j = 1`, and conjugation is injective.
2. **Reuse.** `Matching/MatchingPreparation` applies verbatim to
   `D.withDistinguished t ht`.
   - `distinguishedPerm n` is `A_n(t)` by `rfl`.
   - `matchTarget n B` is `(refineIndex (A_n t) B).block` by `rfl`.
3. **Injectivity.**
   - `acceptable_target_dominates` gives `2|q(B) ∆ T| < |T|` for each acceptable `B`.
   - Images of distinct components are disjoint, so `matching_injective` forbids a
     common target.
   - This proof runs at every index past the matching start, not only at the
     shifted index `matchingIndex n` of `acceptableTargets_injOn`.
4. **Defects.**
   - Source: `refinementPartialBijection_sourceDefect` and the leakage conjunct of
     `ComponentAcceptable`.
   - Symmetric difference: `acceptable_symmDiff_le`, with `2η_n < 1` from
     `matchingStart_spec`.
   - Target: `refinementPartialBijection_targetDefect` and
     `BlockIndex.card_sub_overlap_le_card_symmDiff`, which gives
     `|T| - |q(B) ∩ T| ≤ |q(B) ∆ T|`.
5. **Masses.** `discardedComponentMass_negligible` on `D.withDistinguished t ht`,
   and `badClusterComponentMass_negligible` on the Γ-decomposition.
