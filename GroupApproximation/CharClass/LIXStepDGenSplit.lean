import GroupApproximation.CharClass.ParityEvenLixSplitting
import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.Meta.AxiomGuard

/-!
# `split` for the rank-`n` mapping torus

Lane `lix-evenside-n` (residual (b) of `Gen.lemmaTwoFor_powers_two_lixChernOf`: the field
`split` of `Gen.WuStepDData` at `KGen.lixN`).

`Wu.hasSplitting_lix` is the splitting principle for the mod-2 Chern classes of the rank-two
mapping torus over `lixN dd`.  Its proof never uses the rank of the sphere factor:
`Wu.hasSplitting_flag` asks for a compact non-empty base and a bundle of constant positive rank,
and `Wu.hasSplitting_of_component` absorbs the degreewise round trip `TotalH.of ∘
TotalH.component` through which `lixChernOf` presents the classes.  This file is that proof over
`KGen.lixN n dd = S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`, with `KGen.lixChern_mappingTorus` and
`KGen.lixChernOf_mappingTorus` in place of their rank-two spellings.

## Main declarations

* `Gen.hasSplitting_lixN` — **the field `split` of `Gen.WuStepDData`** for the mod-2 Chern
  classes of the rank-`n` mapping torus.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace Gen

open CategoryTheory
open GroupApproximation.STW59

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **`split` for the rank-`n` mapping torus.**  The bundle has constant rank
`(∑ⱼ dⱼ) + (n + 1)` over the compact non-empty base `S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`, so
`Wu.hasSplitting_flag` applies; `KGen.lixChern_mappingTorus` identifies its Chern classes with
the degreewise ones, and `Wu.hasSplitting_of_component` absorbs the round trip through which
`KGen.lixChernOf` presents them. -/
theorem hasSplitting_lixN (n : ℕ) (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ)
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m)) :
    Wu.HasSplitting (KGen.lixN n dd)
      (KGen.lixChernOf n (KGen.lixChern n dd)
        (mappingTorus (Vmat n) G circHoriz circHeight)) := by
  refine Wu.hasSplitting_congr (fun k => ?_)
    (Wu.hasSplitting_of_component _
      (Wu.hasSplitting_flag
        (⟨mappingTorus (Vmat n) G circHoriz circHeight,
            KGen.continuous_mappingTorus_lix n hGc,
            KGen.isStarProjection_mappingTorus_lix n hGu⟩ :
          Bundle (↥sphereOne × baseM n dd) (VIdx n dd ⊕ VIdx n dd))
        _ (KGen.one_le_lixRank n dd) (fun x => KGen.rank_lixBundle n G hGc hGu x)))
  rw [KGen.lixChernOf_mappingTorus n (KGen.lixChern n dd) hGc hGu k,
    KGen.lixChern_mappingTorus n G hGc hGu (KGen.continuous_mappingTorus_lix n hGc)
      (KGen.isStarProjection_mappingTorus_lix n hGu) k]

end

/-! Audited on every build. -/

#audit_axioms Gen.hasSplitting_lixN

end Gen
end CharClass
end GroupApproximation
