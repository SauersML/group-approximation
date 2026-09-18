import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.HKTAmbientAction

/-!
# The action of an affine isometric action on the Higson--Kasparov--Trout algebra

Lane TWWUCT-C (WO-TWWUCT-C).  The ambient automorphisms `α_g` of `ℝ × H →ᵇ C` carry stage
generators to stage generators (`ambientMap_mem_stageGenerators`).  They therefore preserve the
closed ⋆-subalgebra `A(H) = hktSubalgebra H C`, and restrict to an action of `G` on `A(H)` by
⋆-automorphisms (HKT 1998, §4; Higson--Kasparov 2001, §3).

* `hktSubalgebra_le_comap`: `A(H) ≤ α_g⁻¹ (A(H))`.
* `AffineIsometricAction.hktActionEquiv C g : HKTAlgebraOf H C ≃⋆ₐ[ℂ] HKTAlgebraOf H C`.
* `AffineIsometricAction.hktAction C : G →* (HKTAlgebraOf H C ≃⋆ₐ[ℂ] HKTAlgebraOf H C)`.

The action needs no properness hypothesis, which enters only in `hktAlgebra_isProper`.
-/

namespace GroupApproximation.Full.TWWUCT

noncomputable section

universe u v w

namespace AffineIsometricAction

variable {G : Type u} [Group G] {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (b : AffineIsometricAction G H)
variable {C : Type w} [CStarAlgebra C] [CliffordSystem H C]

/-- `α_g` maps `A(H)` into itself. -/
theorem hktSubalgebra_le_comap (g : G) :
    hktSubalgebra H C ≤ (hktSubalgebra H C).comap (b.ambientAct C g) := by
  show (NonUnitalStarAlgebra.adjoin ℂ
    (⋃ E : FinDimAffine H, E.stageGenerators C)).topologicalClosure ≤ _
  refine NonUnitalStarSubalgebra.topologicalClosure_minimal _ ?_ ?_
  · refine NonUnitalStarAlgebra.adjoin_le fun F hF => ?_
    obtain ⟨E, hE⟩ := Set.mem_iUnion.1 hF
    rw [SetLike.mem_coe, NonUnitalStarSubalgebra.mem_comap, ambientAct_apply]
    exact stageGenerators_subset_hktSubalgebra _ (b.ambientMap_mem_stageGenerators g hE)
  · exact IsClosed.preimage (StarAlgEquiv.isometry (b.ambientAct C g)).continuous
      (isClosed_hktSubalgebra (H := H) (C := C))

theorem ambientMap_mem (g : G) {F : ℝ × H →ᵇ C} (hF : F ∈ hktSubalgebra H C) :
    b.ambientMap g F ∈ hktSubalgebra H C := by
  have h := (NonUnitalStarSubalgebra.mem_comap _ _ _).1 (b.hktSubalgebra_le_comap g hF)
  rwa [ambientAct_apply] at h

variable (C) in
/-- The automorphism `α_g` of the Higson--Kasparov--Trout algebra `A(H)`. -/
def hktActionEquiv (g : G) : HKTAlgebraOf H C ≃⋆ₐ[ℂ] HKTAlgebraOf H C where
  toFun F := ⟨b.ambientMap g F, b.ambientMap_mem g F.2⟩
  invFun F := ⟨b.ambientMap g⁻¹ F, b.ambientMap_mem g⁻¹ F.2⟩
  left_inv F := Subtype.ext (by
    show b.ambientMap g⁻¹ (b.ambientMap g (F : ℝ × H →ᵇ C)) = F
    rw [← b.ambientMap_mul, inv_mul_cancel, b.ambientMap_one])
  right_inv F := Subtype.ext (by
    show b.ambientMap g (b.ambientMap g⁻¹ (F : ℝ × H →ᵇ C)) = F
    rw [← b.ambientMap_mul, mul_inv_cancel, b.ambientMap_one])
  map_mul' F F' := Subtype.ext (map_mul (b.ambientAct C g) (F : ℝ × H →ᵇ C) F')
  map_add' F F' := Subtype.ext (map_add (b.ambientAct C g) (F : ℝ × H →ᵇ C) F')
  map_star' F := Subtype.ext (map_star (b.ambientAct C g) (F : ℝ × H →ᵇ C))
  map_smul' c F := Subtype.ext (map_smul (b.ambientAct C g) c (F : ℝ × H →ᵇ C))

theorem coe_hktActionEquiv (g : G) (F : HKTAlgebraOf H C) :
    ((b.hktActionEquiv C g F : HKTAlgebraOf H C) : ℝ × H →ᵇ C) = b.ambientMap g F :=
  rfl

theorem hktActionEquiv_apply_apply (g : G) (F : HKTAlgebraOf H C) (t : ℝ) (y : H) :
    ((b.hktActionEquiv C g F : HKTAlgebraOf H C) : ℝ × H →ᵇ C) (t, y) =
      CliffordSystem.orth (C := C) (b.linearPart g) ((F : ℝ × H →ᵇ C) (t, b.act g⁻¹ y)) :=
  rfl

variable (C) in
/-- **The action of `G` on the Higson--Kasparov--Trout algebra** `A(H)` induced by an affine
isometric action `b` of `G` on `H` (HKT 1998, §4; Higson--Kasparov 2001, §3). -/
def hktAction : G →* (HKTAlgebraOf H C ≃⋆ₐ[ℂ] HKTAlgebraOf H C) where
  toFun := b.hktActionEquiv C
  map_one' := StarAlgEquiv.ext fun F => Subtype.ext (b.ambientMap_one (F : ℝ × H →ᵇ C))
  map_mul' g h := StarAlgEquiv.ext fun F =>
    Subtype.ext (b.ambientMap_mul g h (F : ℝ × H →ᵇ C))

theorem hktAction_apply (g : G) (F : HKTAlgebraOf H C) :
    b.hktAction C g F = b.hktActionEquiv C g F :=
  rfl

theorem coe_hktAction_apply (g : G) (F : HKTAlgebraOf H C) :
    ((b.hktAction C g F : HKTAlgebraOf H C) : ℝ × H →ᵇ C) = b.ambientMap g F :=
  rfl

end AffineIsometricAction

end

end GroupApproximation.Full.TWWUCT
