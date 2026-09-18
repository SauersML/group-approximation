import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionExtBoundaryDescendExt
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionRosenbergSchochetNaturalPrecomp

/-!
# Naturality of the boundary maps of `Ext` in the first variable

Lane `TWWSch3d3-3B`, work order `WO-TWWSchafhauser-3d3-3B`. Manuscript: `non_mf_group_notes.tex`,
`thm:fixed-radical-membership` (l.1376--1378), via C. Schafhauser, J. reine angew. Math. 759
(2020), §§4--5.

For `ξ ∈ Ext(B, J)` and `φ : A → B`, the index map `∂₀ : K₀ → K₁J` and the exponential map
`∂₁ : K₁ → K₀J` satisfy

  `∂_i (φ^* ξ) = ∂_i ξ ∘ φ_*`.

References: J. Rosenberg, C. Schochet, Duke Math. J. 55 (1987), §1; B. Blackadar, *K-theory for
operator algebras*, 17.1.2, 19.5.7; M. Rørdam, F. Larsen, N. Laustsen, *An introduction to
K-theory for C⋆-algebras*, 9.1.5, 12.2.2.

Proof. The pullback extension algebra of `x ∘ φ` maps to that of `x` by `id × φ⁺`. This map is
the identity on the ideal `J ⊗ 𝒦` and lies over `φ⁺` on the quotients. Naturality of the
generic index and exponential maps (`boundaryZeroOf_natural`, `boundaryOneOf_natural`) then
gives the identity for Busby cycles, and `ExtGroup.natural_of_mk` extends it to `Ext`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

section StarMap

variable {A B : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The unitized map `φ⁺` preserves the scalar part. -/
theorem unitization_starMap_fst (φ : A →⋆ₙₐ[ℂ] B) (p : Unitization ℂ A) :
    (Unitization.starMap φ p).fst = p.fst := by
  show ((Unitization.inl p.fst : Unitization ℂ B) + (φ p.snd : Unitization ℂ B)).fst = p.fst
  rw [Unitization.fst_add, Unitization.fst_inl, Unitization.fst_inr, add_zero]

/-- The unitized map `φ⁺` acts by `φ` on the non-unital part. -/
theorem unitization_starMap_snd (φ : A →⋆ₙₐ[ℂ] B) (p : Unitization ℂ A) :
    (Unitization.starMap φ p).snd = φ p.snd := by
  show ((Unitization.inl p.fst : Unitization ℂ B) + (φ p.snd : Unitization ℂ B)).snd = φ p.snd
  rw [Unitization.snd_add, Unitization.snd_inl, Unitization.snd_inr, zero_add]

end StarMap

section Cycles

variable {A B : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- `id × φ⁺` maps the pullback algebra of `x ∘ φ` into the pullback algebra of `x`. -/
theorem BusbyCycle.comap_mem_extSubalgebra (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J)
    {p : StdBdd J × Unitization ℂ A} (hp : p ∈ (x.comap φ).extSubalgebra) :
    ((p.1, Unitization.starMap φ p.2) : StdBdd J × Unitization ℂ B) ∈ x.extSubalgebra := by
  rw [BusbyCycle.mem_extSubalgebra_iff] at hp ⊢
  show CompactEq J p.1.1 (Adjointable.add
    (Adjointable.smul (Unitization.starMap φ p.2).fst 1) (x.lift (Unitization.starMap φ p.2).snd))
  rw [unitization_starMap_fst, unitization_starMap_snd]
  exact hp

/-- **The comparison map** `E_{x ∘ φ} → E_x`, `(T, s) ↦ (T, φ⁺ s)`, between the pullback
extension algebras. -/
noncomputable def BusbyCycle.comapExtMap (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J) :
    (x.comap φ).extAlgebra →⋆ₐ[ℂ] x.extAlgebra :=
  BusbyCycle.extMap (x.comap φ) x (StarAlgHom.id ℂ (StdBdd J)) (Unitization.starMap φ)
    (fun _ hp => x.comap_mem_extSubalgebra φ hp)

/-- The comparison map lies over `φ⁺`. -/
theorem BusbyCycle.extQuot_comapExtMap (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J)
    (e : (x.comap φ).extAlgebra) :
    x.extQuot (x.comapExtMap φ e) = Unitization.starMap φ ((x.comap φ).extQuot e) :=
  BusbyCycle.extQuot_extMap (x.comap φ) x _ _ _ e

/-- The comparison map is the identity on the ideal `J ⊗ 𝒦`. -/
theorem BusbyCycle.comapExtMap_extIncl (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J)
    (j : StdCpt J) :
    x.comapExtMap φ ((x.comap φ).extIncl j) = x.extIncl (NonUnitalStarAlgHom.id ℂ (StdCpt J) j) :=
  BusbyCycle.extMap_extIncl_id (x.comap φ) x _ _ j

/-- **Naturality of the index map for Busby cycles:** `∂₀(x ∘ φ) = ∂₀(x) ∘ φ_*`. -/
theorem BusbyCycle.boundaryZero_comap (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J) :
    (x.comap φ).boundaryZero = x.boundaryZero.comp (KZeroN.map φ) := by
  refine AddMonoidHom.ext fun w => ?_
  rw [BusbyCycle.boundaryZero_def, BusbyCycle.boundaryZero_def]
  show (stdCornerKOneEquiv J).symm
      (boundaryZeroOf (x.comap φ).extQuot (x.comap φ).extIncl (x.comap φ).extQuot_surjective
        (x.comap φ).extIncl_injective (x.comap φ).extQuot_eq_zero_iff (KZeroN.incl w)) =
    (stdCornerKOneEquiv J).symm
      (boundaryZeroOf x.extQuot x.extIncl x.extQuot_surjective x.extIncl_injective
        x.extQuot_eq_zero_iff (KTheory.KZero.map (starRingHomOf (Unitization.starMap φ))
          (KZeroN.incl w)))
  rw [boundaryZeroOf_natural (x.comap φ).extQuot_surjective (x.comap φ).extIncl_injective
    (x.comap φ).extQuot_eq_zero_iff x.extQuot_surjective x.extIncl_injective
    x.extQuot_eq_zero_iff (x.comapExtMap φ) (Unitization.starMap φ)
    (NonUnitalStarAlgHom.id ℂ (StdCpt J)) (x.extQuot_comapExtMap φ) (x.comapExtMap_extIncl φ)
    (KZeroN.incl w), KOneN.map_id]
  rfl

/-- **Naturality of the exponential map for Busby cycles:** `∂₁(x ∘ φ) = ∂₁(x) ∘ φ_*`. -/
theorem BusbyCycle.boundaryOne_comap (φ : A →⋆ₙₐ[ℂ] B) (x : BusbyCycle B J) :
    (x.comap φ).boundaryOne = x.boundaryOne.comp (KOneN.map φ) := by
  have key := boundaryOneOf_natural (π := (x.comap φ).extQuot) (ι := (x.comap φ).extIncl)
    (hπ := (x.comap φ).extQuot_surjective) (hι := (x.comap φ).extIncl_injective)
    (hex := (x.comap φ).extQuot_eq_zero_iff) (π' := x.extQuot) (ι' := x.extIncl)
    (hπ' := x.extQuot_surjective) (hι' := x.extIncl_injective) (hex' := x.extQuot_eq_zero_iff)
    (x.comapExtMap φ) (Unitization.starMap φ) (NonUnitalStarAlgHom.id ℂ (StdCpt J))
    (x.extQuot_comapExtMap φ) (x.comapExtMap_extIncl φ)
  rw [KZeroN.map_id] at key
  refine AddMonoidHom.ext fun w => ?_
  rw [BusbyCycle.boundaryOne_def, BusbyCycle.boundaryOne_def]
  show (stdCornerKZeroEquiv J).symm
      (boundaryOneOf (x.comap φ).extQuot (x.comap φ).extIncl (x.comap φ).extQuot_surjective
        (x.comap φ).extIncl_injective (x.comap φ).extQuot_eq_zero_iff w) =
    (stdCornerKZeroEquiv J).symm
      ((boundaryOneOf x.extQuot x.extIncl x.extQuot_surjective x.extIncl_injective
        x.extQuot_eq_zero_iff).comp
          (MonoidHom.toAdditive (GroupApproximation.KOne.map (Unitization.starMap φ))) w)
  rw [key]
  rfl

end Cycles

section ExtGroup

variable {A B : Type} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable {J : Type} [NonUnitalCStarAlgebra J] [PartialOrder J] [StarOrderedRing J]

/-- **Naturality of the index map on `Ext`** (Rosenberg–Schochet §1):
`∂₀(φ^* ξ) = ∂₀(ξ) ∘ φ_* : K₀(A) → K₁(J)`. -/
theorem ExtGroup.boundaryZero_comap (φ : A →⋆ₙₐ[ℂ] B) (ξ : ExtGroup B J) :
    ExtGroup.boundaryZero A J (ExtGroup.comap φ ξ) =
      (ExtGroup.boundaryZero B J ξ).comp (KZeroN.map φ) :=
  ExtGroup.natural_of_mk φ (ExtGroup.boundaryZero A J) (ExtGroup.boundaryZero B J)
    (KZeroN.map φ)
    (fun x => by
      rw [ExtGroup.boundaryZero_mk, ExtGroup.boundaryZero_mk]
      exact BusbyCycle.boundaryZero_comap φ x)
    ξ

/-- **Naturality of the exponential map on `Ext`** (Rosenberg–Schochet §1):
`∂₁(φ^* ξ) = ∂₁(ξ) ∘ φ_* : K₁(A) → K₀(J)`. -/
theorem ExtGroup.boundaryOne_comap (φ : A →⋆ₙₐ[ℂ] B) (ξ : ExtGroup B J) :
    ExtGroup.boundaryOne A J (ExtGroup.comap φ ξ) =
      (ExtGroup.boundaryOne B J ξ).comp (KOneN.map φ) :=
  ExtGroup.natural_of_mk φ (ExtGroup.boundaryOne A J) (ExtGroup.boundaryOne B J)
    (KOneN.map φ)
    (fun x => by
      rw [ExtGroup.boundaryOne_mk, ExtGroup.boundaryOne_mk]
      exact BusbyCycle.boundaryOne_comap φ x)
    ξ

end ExtGroup

end GroupApproximation.Full.TWWSchafhauser
