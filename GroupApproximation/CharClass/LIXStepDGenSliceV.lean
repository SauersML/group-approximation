import GroupApproximation.CharClass.LIXStepDGenSlice
import GroupApproximation.CharClass.SliceGenValue
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-`n` mapping torus on the slice is `V`, and its classes are the slice polynomial

Lane `lx-slice2` of the LIX strongest swarm: the last step of the `slice` field of
`Gen.WuStepDData` at `KGen.lixN n dd`.

`CharClass/LIXStepDGenSlice.lean` reduced the classes restricted along the slice to the
degreewise classes of the restricted bundle.  On the south polar slice that bundle is
`0 ⊕ V` on the nose, which is `V` pushed along the second-summand inclusion, so its classes
are those of `V` over the projective base (`LH.chernOf_congr` for the equality,
`LH.chernOf_pushforward` for the change of index type).  lx-integrator's leaf
`Gen.vSliceValue_sliceGen` gives their value.

## Main declarations

* `Gen.chernOf_lixSliceN_eq_vBundleY` — **the bridge**, the rank-`n` form of
  `LH.chernOf_lixSlice_eq_vBundleY`.
* `Gen.map_lixSliceN_lixChernOf_eq_sliceClass` — the ring-valued classes restricted along the
  slice are the coefficients of `∏ⱼ (1 + hⱼ)^{dⱼ}`.
-/

noncomputable section

namespace GroupApproximation
namespace CharClass
namespace Gen

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

set_option linter.unusedSectionVars false

variable {ℓ : ℕ}

/-- **The restricted mapping torus has the classes of `V`.**  At the south pole the
restriction equals `0 ⊕ V`, which is `V` pushed along `Sum.inr`; the classes do not see the
change of index type. -/
theorem chernOf_lixSliceN_eq_vBundleY (n : ℕ) {dd : Fin ℓ → ℕ}
    (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m)) (q : ↥(unitVectors (Fin (n + 1))))
    (k : ℕ) :
    LH.chernOf (comap (lixSliceMapN n dd southPole q) (KGen.lixBundle n G hGc hGu))
        (KGen.lixRank n dd) (fun _ => KGen.rank_lixBundle n G hGc hGu _)
        (KGen.one_le_lixRank n dd) k
      = LH.chernOf (vBundleY n dd) (KGen.lixRank n dd) (rank_vBundleY n dd)
        (KGen.one_le_lixRank n dd) k := by
  have hpt : ∀ y : baseY dd,
      (comap (lixSliceMapN n dd southPole q) (KGen.lixBundle n G hGc hGu)) y
        = (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
            (vBundleY n dd)) y := fun y =>
    (mappingTorus_lixSliceN n G (q, y)).trans
      (LH.pushforward_inr_eq_fromBlocks (VmatY n y)).symm
  have hrank : ∀ y : baseY dd,
      (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
        (vBundleY n dd)).rank y = KGen.lixRank n dd := fun y =>
    (LH.rank_pushforward _ Sum.inr_injective (vBundleY n dd) y).trans (rank_vBundleY n dd y)
  exact (LH.chernOf_congr hpt (KGen.lixRank n dd) (fun _ => KGen.rank_lixBundle n G hGc hGu _)
      hrank (KGen.one_le_lixRank n dd) k).trans
    (LH.chernOf_pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
      (vBundleY n dd) (KGen.lixRank n dd) (rank_vBundleY n dd) hrank
      (KGen.one_le_lixRank n dd) k)

/-- **The classes restricted along the slice are the slice polynomial's coefficients**, at
the generators `LH.sliceGen`. -/
theorem map_lixSliceN_lixChernOf_eq_sliceClass (n : ℕ) {dd : Fin ℓ → ℕ}
    (hdd : ∀ j, 0 < dd j) {G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ}
    (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
    (q : ↥(unitVectors (Fin (n + 1)))) (k : ℕ) :
    TotalH.map (lixSliceN n dd southPole q)
        (KGen.lixChernOf n (KGen.lixChern n dd)
          (mappingTorus (Vmat n) G circHoriz circHeight) k)
      = (sliceClass (Finset.univ : Finset (Fin ℓ)) (LH.sliceGen dd hdd) dd).coeff k := by
  rw [map_lixSliceN_lixChernOf n hGc hGu southPole q k,
    chernOf_lixSliceN_eq_vBundleY n G hGc hGu q k]
  exact vSliceValue_sliceGen n dd hdd k

end Gen

/-! Audited on every build. -/

#audit_axioms Gen.chernOf_lixSliceN_eq_vBundleY
#audit_axioms Gen.map_lixSliceN_lixChernOf_eq_sliceClass

end CharClass
end GroupApproximation

end
