import GroupApproximation.CharClass.LIXKGenChern
import GroupApproximation.CharClass.ChernOfInvariance
import GroupApproximation.CharClass.LIXChernSliceValueBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# The rank-`n` mapping torus on a polar slice, at the level of Chern classes

Lane `lx-slice2` of the LIX strongest swarm: the `slice` field of `Gen.WuStepDData` at
`KGen.lixN n dd = S¹ × S^{2n+1} × ∏ⱼ ℂP^{dⱼ}`.

The rank-two proof never used the rank of the sphere factor, so each declaration here is its
rank-two counterpart with the rank a parameter:

* `lixSliceMapN`, `lixSliceN` — the slice `y ↦ (p₁, (q, y))`, as a continuous map and as a
  morphism into `KGen.lixN n dd` (`LIXChernSlice.lixSliceMap`, `CohomologyLIXSliceBridge.lixSlice`).
* `pull_lixChern_lixSliceN` — naturality of `KGen.lixChern` along it (`pull_lixChern_lixSlice`).
* `mappingTorus_lixSliceN` — on the south polar slice the mapping torus is `0 ⊕ V` on the
  nose: the horizontal coordinate vanishes, so the clutching field drops out before any block
  algebra runs (`mappingTorus_lixSlice`).
* `map_lixSliceN_lixChernOf` — the ring-valued classes restricted along the slice are the
  degreewise classes of the restricted bundle, in their degree.

The value of those classes is the value for `V` over the projective base, which is not here.
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

/-! ## 1. The slice -/

/-- **The slice of `S¹ × S^{2n+1} × Y`** at a point of the circle and a point of the odd
sphere, as a continuous map of the concrete bases, the shape `Bundle.comap` consumes. -/
def lixSliceMapN (n : ℕ) (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q : ↥(unitVectors (Fin (n + 1)))) : C(baseY dd, ↥sphereOne × baseM n dd) :=
  ⟨fun y => (p1, (q, y)), continuous_const.prodMk (continuous_const.prodMk continuous_id)⟩

/-- The slice as a morphism into `KGen.lixN n dd`, the space the classes live on. -/
def lixSliceN (n : ℕ) (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q : ↥(unitVectors (Fin (n + 1)))) : TopCat.of (baseY dd) ⟶ KGen.lixN n dd :=
  cmap (lixSliceMapN n dd p1 q)

theorem cmap_lixSliceMapN (n : ℕ) (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q : ↥(unitVectors (Fin (n + 1)))) :
    cmap (lixSliceMapN n dd p1 q) = lixSliceN n dd p1 q := rfl

/-! ## 2. Naturality along the slice -/

/-- **Naturality of `KGen.lixChern` along the slice.**  For a family of constant positive
rank, the classes restricted to the slice are the classes of the restricted family over the
projective base.  The rank hypothesis is `KGen.lixChern`'s branch condition. -/
theorem pull_lixChern_lixSliceN (n : ℕ) (dd : Fin ℓ → ℕ) (p1 : ↥sphereOne)
    (q : ↥(unitVectors (Fin (n + 1)))) (P : KGen.LixFamily n dd) (hcont : Continuous P)
    (hproj : ∀ p, IsStarProjection (P p)) (s : ℕ) (hs1 : 1 ≤ s)
    (hs : ∀ x, (⟨P, hcont, hproj⟩ :
      Bundle (↥sphereOne × baseM n dd) (VIdx n dd ⊕ VIdx n dd)).rank x = s) (k : ℕ) :
    pull (lixSliceN n dd p1 q) (2 * k) (KGen.lixChern n dd P hcont hproj k)
      = LH.chernOf (comap (lixSliceMapN n dd p1 q)
          (⟨P, hcont, hproj⟩ : Bundle (↥sphereOne × baseM n dd) (VIdx n dd ⊕ VIdx n dd))) s
          (fun y => hs (lixSliceMapN n dd p1 q y)) hs1 k := by
  have hcomap := LH.chern_comap (lixSliceMapN n dd p1 q)
    (⟨P, hcont, hproj⟩ : Bundle (↥sphereOne × baseM n dd) (VIdx n dd ⊕ VIdx n dd))
    s hs hs1 k
  have h2 : LH.chernOf (comap (lixSliceMapN n dd p1 q)
        (⟨P, hcont, hproj⟩ : Bundle (↥sphereOne × baseM n dd) (VIdx n dd ⊕ VIdx n dd))) s
        (fun y => hs (lixSliceMapN n dd p1 q y)) hs1 k
      = pull (cmap (lixSliceMapN n dd p1 q)) (2 * k)
          (TotalH.component (TopCat.of (↥sphereOne × baseM n dd)) (2 * k)
            ((LHCast.lerayHirschData_of_graded
              (LH.lerayHirschGraded_compact
                (⟨P, hcont, hproj⟩ :
                  Bundle (↥sphereOne × baseM n dd) (VIdx n dd ⊕ VIdx n dd))
                s hs hs1)).chern k)) := by
    simp only [LH.chernOf]
    rw [hcomap, Wu.totalH_component_map]
  rw [KGen.lixChern_eq_of_rank n P hcont hproj s hs1 hs k]
  exact h2.symm

/-! ## 3. The slice equation -/

/-- **On the south polar slice the rank-`n` mapping torus is `0 ⊕ V`, on the nose.**  The
clutching field is absent: the horizontal coordinate vanishes at the pole. -/
theorem mappingTorus_lixSliceN (n : ℕ) {dd : Fin ℓ → ℕ}
    (G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ) (m : baseM n dd) :
    mappingTorus (Vmat n) G circHoriz circHeight (southPole, m)
      = Matrix.fromBlocks 0 0 0 (Vmat n m) :=
  mappingTorus_south circHoriz_southPole circHeight_southPole m

/-! ## 4. The ring-valued classes on the slice -/

/-- **The ring-valued classes restricted along the slice** are the degreewise classes of the
restricted bundle, placed in their degree. -/
theorem map_lixSliceN_lixChernOf (n : ℕ) {dd : Fin ℓ → ℕ}
    {G : baseM n dd → Matrix (VIdx n dd) (VIdx n dd) ℂ} (hGc : Continuous G)
    (hGu : ∀ m, IsCornerUnitary (Vmat n m) (G m)) (p1 : ↥sphereOne)
    (q : ↥(unitVectors (Fin (n + 1)))) (k : ℕ) :
    TotalH.map (lixSliceN n dd p1 q)
        (KGen.lixChernOf n (KGen.lixChern n dd)
          (mappingTorus (Vmat n) G circHoriz circHeight) k)
      = TotalH.of (TopCat.of (baseY dd)) (2 * k)
          (LH.chernOf (comap (lixSliceMapN n dd p1 q) (KGen.lixBundle n G hGc hGu))
            (KGen.lixRank n dd) (fun y => KGen.rank_lixBundle n G hGc hGu _)
            (KGen.one_le_lixRank n dd) k) := by
  rw [KGen.lixChernOf_mappingTorus n (KGen.lixChern n dd) hGc hGu k, TotalH.map_of]
  exact congrArg (TotalH.of (TopCat.of (baseY dd)) (2 * k))
    (pull_lixChern_lixSliceN n dd p1 q (mappingTorus (Vmat n) G circHoriz circHeight)
      (KGen.continuous_mappingTorus_lix n hGc) (KGen.isStarProjection_mappingTorus_lix n hGu)
      (KGen.lixRank n dd) (KGen.one_le_lixRank n dd)
      (fun x => KGen.rank_lixBundle n G hGc hGu x) k)

end Gen

/-! Audited on every build. -/

#audit_axioms Gen.pull_lixChern_lixSliceN
#audit_axioms Gen.mappingTorus_lixSliceN
#audit_axioms Gen.map_lixSliceN_lixChernOf

end CharClass
end GroupApproximation

end
