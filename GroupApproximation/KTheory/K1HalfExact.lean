import GroupApproximation.KTheory.K1Lift
import GroupApproximation.KTheory.K1Scalar
import GroupApproximation.Analysis.CStarIdealApproximateUnit
import GroupApproximation.Analysis.CStarQuotientHom
import GroupApproximation.Analysis.CStarMinTensorQuotient
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# Half-exactness of `K_1`

Let `I` be a closed star-stable two-sided ideal of a unital C⋆-algebra `A`, and put
`K_1(I) := K_1(Ĩ)` with `Ĩ = Unitization ℂ (idealStarSub I)`.  The unital ⋆-homomorphism
`ι : Ĩ → A`, `(λ, x) ↦ λ 1 + x`, and the quotient map `π : A → A ⧸ I` give

  `K_1(I) → K_1(A) → K_1(A ⧸ I)`,

and this sequence is exact: `range (K_1 ι) = ker (K_1 π)`.

* The composite `π ∘ ι` factors through the scalar map `Ĩ → ℂ`, and `K_1(ℂ) = 0`.
* If `[u] ∈ K_1(A)` dies in `K_1(A ⧸ I)`, then `π (diag (u, 1))` lies in `U_0` at some level `k`;
  lift it to `w ∈ U_0(M_k A)`.  Then `v = diag (u, 1) w⁻¹` has the same class as `u`, and
  `π v = 1`, so every entry of `v - 1` lies in `I` and `v` is the image of a unitary over `Ĩ`.
-/

namespace GroupApproximation

universe u

noncomputable section

open CStarTensor

namespace GroupTower

variable {G : ℕ → Type u} [∀ n, Group (G n)] (T : GroupTower G)

/-- An element of a level that becomes trivial in the colimit is already trivial at a later
level. -/
theorem exists_map_eq_one_of_mkAt_eq_one {n : ℕ} {x : G n} (h : T.mkAt n x = 1) :
    ∃ (k : ℕ) (hk : n ≤ k), T.map hk x = 1 := by
  have h' : Quotient.mk T.setoid ⟨n, x⟩ = Quotient.mk T.setoid ⟨0, (1 : G 0)⟩ := h
  obtain ⟨k, hx, hy, e⟩ := Quotient.exact h'
  exact ⟨k, hx, e.trans (map_one _)⟩

end GroupTower

section Trivial

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_kOneMap_eq_one_of_kOneIota_eq_one {n : ℕ} {x : KOneLevel A n}
    (h : kOneIota A n x = 1) : ∃ (k : ℕ) (hk : n ≤ k), kOneMap A hk x = 1 :=
  (kOneTower A).exists_map_eq_one_of_mkAt_eq_one h

end Trivial

theorem algebraMap_cstarMat_one_apply {A : Type u} [CStarAlgebra A] (n : ℕ) (i j : Fin n) :
    algebraMap ℂ A ((1 : CStarMat n ℂ) i j) = (1 : CStarMat n A) i j :=
  congrArg (fun M : CStarMat n A => M i j) (map_one (matMapHom (StarAlgHom.ofId ℂ A) n))

section Ideal

variable {A : Type u} [CStarAlgebra A] (I : Ideal A) [IsStarStable I]

/-- The unital ⋆-homomorphism `Ĩ → A`, `(λ, x) ↦ λ 1 + x`. -/
def idealUnitizationIncl : Unitization ℂ (idealStarSub I) →⋆ₐ[ℂ] A :=
  Unitization.starLift (NonUnitalStarSubalgebraClass.subtype (R := ℂ) (idealStarSub I))

theorem idealUnitizationIncl_apply (x : Unitization ℂ (idealStarSub I)) :
    idealUnitizationIncl I x = algebraMap ℂ A x.fst + (x.snd : A) := rfl

/-- The scalar part `Ĩ → ℂ`, `(λ, x) ↦ λ`. -/
def idealUnitizationScalar : Unitization ℂ (idealStarSub I) →⋆ₐ[ℂ] ℂ :=
  Unitization.starLift (0 : idealStarSub I →⋆ₙₐ[ℂ] ℂ)

theorem idealUnitizationScalar_apply (x : Unitization ℂ (idealStarSub I)) :
    idealUnitizationScalar I x = x.fst := by
  show algebraMap ℂ ℂ x.fst + (0 : idealStarSub I →⋆ₙₐ[ℂ] ℂ) x.snd = x.fst
  rw [NonUnitalStarAlgHom.zero_apply, add_zero, Algebra.algebraMap_self_apply]

/-- An element of `Ĩ` is determined by its image in `A` and its scalar part. -/
theorem idealUnitization_ext {x y : Unitization ℂ (idealStarSub I)}
    (h₁ : idealUnitizationIncl I x = idealUnitizationIncl I y)
    (h₂ : idealUnitizationScalar I x = idealUnitizationScalar I y) : x = y := by
  rw [idealUnitizationScalar_apply, idealUnitizationScalar_apply] at h₂
  rw [idealUnitizationIncl_apply, idealUnitizationIncl_apply, h₂] at h₁
  exact Unitization.ext h₂ (Subtype.ext (add_left_cancel h₁))

/-- A matrix over `A` congruent to `1` modulo `I`, as a matrix over `Ĩ`. -/
def idealUnitizationMatLift {n : ℕ} (v : CStarMat n A)
    (hv : ∀ i j, v i j - (1 : CStarMat n A) i j ∈ I) :
    CStarMat n (Unitization ℂ (idealStarSub I)) := fun i j =>
  ⟨((1 : CStarMat n ℂ) i j, ⟨v i j - (1 : CStarMat n A) i j, hv i j⟩)⟩

section TwoSided

variable [I.IsTwoSided]

/-- `π ∘ ι` is the scalar part followed by `ℂ → A ⧸ I`. -/
theorem quotientStarMk_comp_idealUnitizationIncl :
    (quotientStarMk I).comp (idealUnitizationIncl I) =
      (StarAlgHom.ofId ℂ (A ⧸ I)).comp (idealUnitizationScalar I) := by
  refine StarAlgHom.ext fun x => ?_
  show quotientStarMk I (idealUnitizationIncl I x) =
    algebraMap ℂ (A ⧸ I) (idealUnitizationScalar I x)
  have hx : ((x.snd : idealStarSub I) : A) ∈ I := x.snd.prop
  rw [idealUnitizationIncl_apply, idealUnitizationScalar_apply, map_add, AlgHomClass.commutes,
    quotientStarMk_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hx, add_zero]

end TwoSided

section Closed

variable [IsClosed (I : Set A)]

theorem idealUnitizationIncl_matLift {n : ℕ} (v : CStarMat n A)
    (hv : ∀ i j, v i j - (1 : CStarMat n A) i j ∈ I) :
    matMapStarAlgHom (idealUnitizationIncl I) n (idealUnitizationMatLift I v hv) = v :=
  CStarMatrix.ext fun i j => by
    show algebraMap ℂ A ((1 : CStarMat n ℂ) i j) + (v i j - (1 : CStarMat n A) i j) = v i j
    rw [algebraMap_cstarMat_one_apply]
    exact add_sub_cancel _ _

theorem idealUnitizationScalar_matLift {n : ℕ} (v : CStarMat n A)
    (hv : ∀ i j, v i j - (1 : CStarMat n A) i j ∈ I) :
    matMapStarAlgHom (idealUnitizationScalar I) n (idealUnitizationMatLift I v hv) = 1 :=
  CStarMatrix.ext fun i j => idealUnitizationScalar_apply I (idealUnitizationMatLift I v hv i j)

theorem matMapStarAlgHom_idealUnitization_ext {n : ℕ}
    {X Y : CStarMat n (Unitization ℂ (idealStarSub I))}
    (h₁ : matMapStarAlgHom (idealUnitizationIncl I) n X =
      matMapStarAlgHom (idealUnitizationIncl I) n Y)
    (h₂ : matMapStarAlgHom (idealUnitizationScalar I) n X =
      matMapStarAlgHom (idealUnitizationScalar I) n Y) : X = Y :=
  CStarMatrix.ext fun i j =>
    idealUnitization_ext I (congrArg (fun M : CStarMat n A => M i j) h₁)
      (congrArg (fun M : CStarMat n ℂ => M i j) h₂)

/-- A unitary congruent to `1` modulo `I` lifts to a unitary over `Ĩ`. -/
theorem idealUnitizationMatLift_mem_unitary {n : ℕ} {v : CStarMat n A}
    (hv : ∀ i j, v i j - (1 : CStarMat n A) i j ∈ I) (hu : v ∈ unitary (CStarMat n A)) :
    idealUnitizationMatLift I v hv ∈ unitary (CStarMat n (Unitization ℂ (idealStarSub I))) := by
  have hι := idealUnitizationIncl_matLift I v hv
  have hσ := idealUnitizationScalar_matLift I v hv
  refine Unitary.mem_iff.mpr ⟨matMapStarAlgHom_idealUnitization_ext I ?_ ?_,
    matMapStarAlgHom_idealUnitization_ext I ?_ ?_⟩
  · rw [map_mul, map_star, hι, map_one]
    exact (Unitary.mem_iff.mp hu).1
  · rw [map_mul, map_star, hσ, map_one, star_one, one_mul]
  · rw [map_mul, map_star, hι, map_one]
    exact (Unitary.mem_iff.mp hu).2
  · rw [map_mul, map_star, hσ, map_one, star_one, mul_one]

section Order

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder (Unitization ℂ (idealStarSub I))]
  [StarOrderedRing (Unitization ℂ (idealStarSub I))]

/-- The class of a unitary congruent to `1` modulo `I` is in the image of `K_1(I)`. -/
theorem exists_kOneMap_idealUnitizationIncl {n : ℕ} (v : unitary (CStarMat n A))
    (hv : ∀ i j, (v : CStarMat n A) i j - (1 : CStarMat n A) i j ∈ I) :
    ∃ y : KOne (Unitization ℂ (idealStarSub I)),
      KOne.map (idealUnitizationIncl I) y = kOneIota A n (QuotientGroup.mk v) := by
  let w : unitary (CStarMat n (Unitization ℂ (idealStarSub I))) :=
    ⟨idealUnitizationMatLift I (v : CStarMat n A) hv,
      idealUnitizationMatLift_mem_unitary I hv v.prop⟩
  have hw : matMapUnitary (idealUnitizationIncl I) n w = v :=
    Subtype.ext (idealUnitizationIncl_matLift I (v : CStarMat n A) hv)
  exact ⟨_, (KOne.map_iota_mk (idealUnitizationIncl I) n w).trans (by rw [hw])⟩

end Order

section Quotient

variable [I.IsTwoSided] [Nontrivial A]

/-- A unitary killed by `π` is congruent to `1` modulo `I`. -/
theorem sub_one_mem_of_matMapUnitary_eq_one {n : ℕ} {v : unitary (CStarMat n A)}
    (hv : matMapUnitary (quotientStarMk I) n v = 1) (i j : Fin n) :
    (v : CStarMat n A) i j - (1 : CStarMat n A) i j ∈ I := by
  have h : matMapHom (quotientStarMk I) n (v : CStarMat n A) =
      matMapHom (quotientStarMk I) n 1 := by
    rw [map_one]
    exact congrArg Subtype.val hv
  have hij : Ideal.Quotient.mk I ((v : CStarMat n A) i j) =
      Ideal.Quotient.mk I ((1 : CStarMat n A) i j) :=
    congrArg (fun M : CStarMat n (A ⧸ I) => M i j) h
  exact Ideal.Quotient.eq.mp hij

section Order

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder (Unitization ℂ (idealStarSub I))]
  [StarOrderedRing (Unitization ℂ (idealStarSub I))] [PartialOrder (A ⧸ I)]
  [StarOrderedRing (A ⧸ I)]

/-- **`K_1(I) → K_1(A) → K_1(A ⧸ I)` is a complex.** -/
theorem kOne_map_quotient_map_idealUnitizationIncl (y : KOne (Unitization ℂ (idealStarSub I))) :
    KOne.map (quotientStarMk I) (KOne.map (idealUnitizationIncl I) y) = 1 := by
  letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  haveI : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  have hc : KOne.map ((quotientStarMk I).comp (idealUnitizationIncl I)) =
      KOne.map ((StarAlgHom.ofId ℂ (A ⧸ I)).comp (idealUnitizationScalar I)) :=
    congrArg (KOne.map (A := Unitization ℂ (idealStarSub I)) (B := A ⧸ I))
      (quotientStarMk_comp_idealUnitizationIncl I)
  calc KOne.map (quotientStarMk I) (KOne.map (idealUnitizationIncl I) y)
      = KOne.map ((quotientStarMk I).comp (idealUnitizationIncl I)) y :=
        (DFunLike.congr_fun (KOne.map_comp (quotientStarMk I) (idealUnitizationIncl I)) y).symm
    _ = KOne.map (StarAlgHom.ofId ℂ (A ⧸ I)) (KOne.map (idealUnitizationScalar I) y) :=
        (DFunLike.congr_fun hc y).trans (DFunLike.congr_fun
          (KOne.map_comp (StarAlgHom.ofId ℂ (A ⧸ I)) (idealUnitizationScalar I)) y)
    _ = 1 := by rw [kOne_complex_eq_one (KOne.map (idealUnitizationScalar I) y), map_one]

/-- **Exactness at `K_1(A)`, the lifting half.** -/
theorem exists_kOne_map_idealUnitizationIncl_of_map_eq_one {x : KOne A}
    (hx : KOne.map (quotientStarMk I) x = 1) :
    ∃ y : KOne (Unitization ℂ (idealStarSub I)), KOne.map (idealUnitizationIncl I) y = x := by
  obtain ⟨n, c, rfl⟩ := (kOneTower A).exists_iota x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective c
  have hx' : kOneIota (A ⧸ I) n (QuotientGroup.mk (matMapUnitary (quotientStarMk I) n u)) = 1 :=
    hx
  obtain ⟨k, hk, hu⟩ := exists_kOneMap_eq_one_of_kOneIota_eq_one hx'
  have hu0 : matMapUnitary (quotientStarMk I) k (blockOneUnitary hk u) ∈
      unitaryComponentOne (CStarMat k (A ⧸ I)) := by
    have h0 : blockOneUnitary hk (matMapUnitary (quotientStarMk I) n u) ∈
        unitaryComponentOne (CStarMat k (A ⧸ I)) :=
      (QuotientGroup.eq_one_iff (blockOneUnitary hk (matMapUnitary (quotientStarMk I) n u))).mp hu
    rwa [show blockOneUnitary hk (matMapUnitary (quotientStarMk I) n u) =
      matMapUnitary (quotientStarMk I) k (blockOneUnitary hk u) from
        Subtype.ext (matMapHom_blockOne (quotientStarMk I) (u : CStarMat n A) k).symm] at h0
  obtain ⟨w, hw, hwu⟩ := exists_matMapUnitary_lift (quotientStarMk_surjective I) k hu0
  have hv1 : matMapUnitary (quotientStarMk I) k (blockOneUnitary hk u * w⁻¹) = 1 := by
    rw [map_mul, map_inv, hwu, mul_inv_cancel]
  obtain ⟨y, hy⟩ := exists_kOneMap_idealUnitizationIncl I (blockOneUnitary hk u * w⁻¹)
    (sub_one_mem_of_matMapUnitary_eq_one I hv1)
  refine ⟨y, hy.trans ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff w).mpr hw, inv_one,
    mul_one]
  exact kOneIota_kOneMap A hk (QuotientGroup.mk u)

/-- **Half-exactness of `K_1`**: `K_1(I) → K_1(A) → K_1(A ⧸ I)` is exact at `K_1(A)`. -/
theorem kOne_range_idealUnitizationIncl_eq_ker :
    (KOne.map (idealUnitizationIncl I)).range = (KOne.map (quotientStarMk I)).ker := by
  ext x
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    exact kOne_map_quotient_map_idealUnitizationIncl I y
  · exact exists_kOne_map_idealUnitizationIncl_of_map_eq_one I

end Order

end Quotient

end Closed

end Ideal

end

end GroupApproximation
