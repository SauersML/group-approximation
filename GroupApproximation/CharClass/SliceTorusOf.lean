import GroupApproximation.CharClass.SliceSplitVOf
import GroupApproximation.CharClass.LIXKGenBundle
import GroupApproximation.CharClass.LIXChernSliceValueBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# The slice field at the real mapping torus, over a field `K`

Lane `lx-sliceK` of the STW Problem LIX strongest-theorem swarm.

`Gen.sliceValue_of_comapOf` (`SliceSplitVOf`) is the slice value for any bundle whose restriction
to a slice is `V` pushed into a larger index.  This file supplies that restriction for the rank-`n`
mapping torus `KGen.lixBundle n G hGc hGu`, over `S¹ × S^{2n+1} × Y` at the doubled index
`VIdx n dd ⊕ VIdx n dd`: on the south polar slice the horizontal coordinate vanishes, the clutching
field drops out, and the projection is `0 ⊕ V` on the nose (`mappingTorus_south`), which is `V`
pushed along `Sum.inr` (`LH.pushforward_inr_eq_fromBlocks`).

The slice is taken as any continuous map `s` with `s y = (southPole, (q, y))`, so that every
spelling of it (`Gen.lixSliceMapN n dd southPole q`, the underlying map of a Künneth slice) meets the
hypothesis by `rfl`.

## Main declarations

* `Gen.comap_lixBundle_eq_pushforward_vBundleY` — **the slice equation, as bundles.**
* `Gen.sliceValue_lixBundleOf` — **the slice field of `Gen.RealBundleModP` at the real mapping torus.**
-/

set_option autoImplicit false

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.LH

set_option linter.unusedSectionVars false

namespace Gen

/-- **The slice equation, as bundles.**  On the south polar slice at the sphere point `q`, the
rank-`n` mapping torus is `V` pushed along the second summand of the doubled index. -/
theorem comap_lixBundle_eq_pushforward_vBundleY (n : ℕ) {ℓ : ℕ} {dd : Fin ℓ → ℕ}
    (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
    (s : C(baseY dd, ↥sphereOne × baseM n dd)) (q : ↥(unitVectors (Fin (n + 1))))
    (hs : ∀ y, s y = (southPole, ((q, y) : baseM n dd))) :
    comap s (KGen.lixBundle n G hGc hGu)
      = pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
          (vBundleY n dd) := by
  refine Bundle.ext fun y => ?_
  rw [comap_apply, hs y]
  exact (mappingTorus_south circHoriz_southPole circHeight_southPole ((q, y) : baseM n dd)).trans
    (LH.pushforward_inr_eq_fromBlocks (VmatY n y)).symm

/-- **The slice field at the real mapping torus.**  The Chern classes over `K` of the rank-`n`
mapping torus, restricted to the south polar slice, are the coefficients of the slice polynomial
`∏ⱼ (1 + hⱼ X)^{dⱼ}`, with `hⱼ = sliceGenPushOf K n Sum.inr _ hgen j`. -/
theorem sliceValue_lixBundleOf (K : Type) [Field K] (n : ℕ) {ℓ : ℕ} (dd : Fin ℓ → ℕ)
    (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ) (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m))
    (s : C(baseY dd, ↥sphereOne × baseM n dd)) (q : ↥(unitVectors (Fin (n + 1))))
    (hs : ∀ y, s y = (southPole, ((q, y) : baseM n dd)))
    (hgen : Hmod K (CPtop (1 + tautCardOf (VIdx n dd ⊕ VIdx n dd))) 2)
    (LE : LerayHirschGraded (projMapOf (KGen.lixBundle n G hGc hGu))
      (LH.tautEulerDualK K hgen (KGen.lixBundle n G hGc hGu)) (KGen.lixRank n dd))
    (LV : LerayHirschGraded
      (projMapOf (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
        (vBundleY n dd)))
      (LH.tautEulerDualK K hgen
        (pushforward (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective
          (vBundleY n dd)))
      (KGen.lixRank n dd))
    (k : ℕ) :
    Gen.evenMap K (cmap s) ((LerayHirschDataEvenOf.of_graded LE).chern k)
      = (sliceClass (Finset.univ : Finset (Fin ℓ))
          (sliceGenPushOf K n (Sum.inr : VIdx n dd → VIdx n dd ⊕ VIdx n dd) Sum.inr_injective hgen)
          dd).coeff k :=
  sliceValue_of_comapOf K n dd hgen (KGen.lixBundle n G hGc hGu) s Sum.inr Sum.inr_injective
    (comap_lixBundle_eq_pushforward_vBundleY n G hGc hGu s q hs) LE LV k

end Gen

#audit_axioms Gen.comap_lixBundle_eq_pushforward_vBundleY
#audit_axioms Gen.sliceValue_lixBundleOf

end GroupApproximation.CharClass
