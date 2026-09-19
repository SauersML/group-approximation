import GroupApproximation.Analysis.FiniteDimensionalCStarMatrixCPRetract
import GroupApproximation.Analysis.HNNTraceStarAlgHomDescent
import GroupApproximation.Analysis.LanceNFUnitalCPAP
import GroupApproximation.Meta.AxiomGuard

/-!
# Extending a finite-dimensional UCP map across a faithful inclusion

The upward-map step in the Blackadar--Kirchberg converse needs to move a
finite-dimensional completely positive map from the image of a faithful
corona representation to the whole corona.  The matrix-target Arveson theorem
already proves the extension after the target is a full operator matrix
algebra.  A finite-dimensional C-star algebra is a UCP retract of one such
matrix algebra, so embedding before Arveson and retracting afterwards gives
the required extension with no supplied analytic input.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

open GroupApproximation.CStarExactness
open scoped InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

universe u w

variable {A : Type u} {B : Type} {D : Type w}
  [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra D]
  [Nontrivial A] [Nontrivial B] [Nontrivial D]
  [FiniteDimensional ℂ D]

local instance matrixBlockCStarAlgebraForArvesonExtension
    (Z : Type) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-! ## The closed represented copy of the source -/

/-- The image of a unital star homomorphism, bundled as a star subalgebra. -/
def starAlgHomRange (e : A →⋆ₐ[ℂ] B) : StarSubalgebra ℂ B where
  carrier := Set.range e
  zero_mem' := ⟨0, e.map_zero⟩
  one_mem' := ⟨1, e.map_one⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, e.map_add a b⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, e.map_mul a b⟩
  algebraMap_mem' := by
    intro c
    exact ⟨algebraMap ℂ A c, e.commutes c⟩
  star_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨star a, map_star e a⟩

omit [Nontrivial A] [Nontrivial B] in
@[simp] theorem mem_starAlgHomRange_iff (e : A →⋆ₐ[ℂ] B) (b : B) :
    b ∈ starAlgHomRange e ↔ b ∈ Set.range e :=
  Iff.rfl

/-- A faithful unital star homomorphism identifies its source with its
represented range. -/
def starAlgEquivRange (e : A →⋆ₐ[ℂ] B) (he : Function.Injective e) :
    A ≃⋆ₐ[ℂ] starAlgHomRange e := by
  let er : A →⋆ₐ[ℂ] starAlgHomRange e :=
    e.codRestrict (starAlgHomRange e) fun a ↦ ⟨a, rfl⟩
  refine StarAlgEquiv.ofBijective er ⟨?_, ?_⟩
  · intro a b hab
    apply he
    exact congrArg Subtype.val hab
  · intro b
    obtain ⟨a, ha⟩ := b.property
    refine ⟨a, Subtype.ext ?_⟩
    exact ha

/-- The represented range of a faithful unital C-star homomorphism is closed. -/
theorem isClosed_starAlgHomRange
    (e : A →⋆ₐ[ℂ] B) :
    IsClosed ((starAlgHomRange e : StarSubalgebra ℂ B) : Set B) := by
  change IsClosed (Set.range e)
  exact HNNTrace.isClosed_range_starAlgHom e

/-! ## Finite-dimensional Arveson extension -/

/-- A UCP map into a nontrivial finite-dimensional C-star algebra extends
across every faithful unital C-star inclusion.

The proof embeds the target into one full matrix algebra, uses the repository's
matrix-target Arveson theorem on the closed represented range, and then applies
the UCP retraction back onto the original finite-dimensional algebra. -/
theorem exists_ucp_extension_finiteDimensional
    (e : A →⋆ₐ[ℂ] B) (he : Function.Injective e)
    (φ : A →ₗ[ℂ] D) (hφcp : IsCompletelyPositive φ) (
      hφone : φ 1 = 1) :
    ∃ Ψ : B →ₗ[ℂ] D,
      IsCompletelyPositive Ψ ∧ Ψ 1 = 1 ∧ ∀ a : A, Ψ (e a) = φ a := by
  classical
  letI : PartialOrder B := CStarAlgebra.spectralOrder B
  letI : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  obtain ⟨R⟩ := exists_matrixUCPRetract_of_finiteDimensionalCStar D
  let C : StarSubalgebra ℂ B := starAlgHomRange e
  have hC : IsClosed (C : Set B) := isClosed_starAlgHomRange e
  letI : CStarAlgebra C :=
    { toNormedRing := inferInstance
      toStarRing := inferInstance
      toCompleteSpace := hC.completeSpace_coe
      toCStarRing := inferInstance
      toNormedAlgebra := C.toSubalgebra.toNormedAlgebra
      toStarModule := StarSubalgebra.starModule C }
  let er : A ≃⋆ₐ[ℂ] C := starAlgEquivRange e he
  let φC : C →ₗ[ℂ] D := φ.comp (starAlgEquivLinearMap er.symm)
  have hφCcp : IsCompletelyPositive φC :=
    isCompletelyPositive_comp_starAlgEquiv er.symm φ hφcp
  let opEquiv : Matrix R.model R.model ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card R.model)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card R.model))) :=
    (matrixReindexStarAlgEquiv (Fintype.equivFin R.model)).trans
      (Matrix.toEuclideanCLM (n := Fin (Fintype.card R.model)) (𝕜 := ℂ))
  let jOpStar : D →⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card R.model)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card R.model))) :=
    opEquiv.toStarAlgHom.comp R.embedding
  let jOp : D →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card R.model)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card R.model))) := jOpStar
  let Φ : C →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card R.model)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card R.model))) := jOp.comp φC
  have hjOpCP : IsCompletelyPositive jOp :=
    isCompletelyPositive_of_starAlgHom jOpStar.toNonUnitalStarAlgHom
  have hΦcp : IsCompletelyPositive Φ := hjOpCP.comp hφCcp
  have hΦform : ∀ (m : ℕ) (a : Fin m → C)
      (v : Fin m → EuclideanSpace ℂ (Fin (Fintype.card R.model))),
      0 ≤ (∑ i : Fin m, ∑ j : Fin m,
        ⟪v i, Φ (star (a i) * a j) (v j)⟫_ℂ).re := by
    intro m a v
    by_cases hm : m = 0
    · subst m
      simp
    · letI : NeZero m := ⟨hm⟩
      exact (hΦcp.form_nonneg a v).1
  have hΦstar : ∀ c : C, Φ (star c) = star (Φ c) :=
    OrderZero.map_star_of_cp hΦcp
  have hφCone : φC 1 = 1 := by
    dsimp only [φC, LinearMap.comp_apply]
    rw [starAlgEquivLinearMap_apply, map_one, hφone]
  have hΦone : Φ 1 = 1 := by
    dsimp only [Φ, jOp, LinearMap.comp_apply]
    rw [hφCone]
    exact jOpStar.map_one
  obtain ⟨Θ, hΘcp, hΘone, hΘext⟩ :=
    exists_ucp_extension C hC Φ
      hΦform hΦstar hΦone
  let fromOp :
      (EuclideanSpace ℂ (Fin (Fintype.card R.model)) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card R.model))) →ₗ[ℂ]
          Matrix R.model R.model ℂ :=
    starAlgEquivLinearMap opEquiv.symm
  let Ψ : B →ₗ[ℂ] D := R.retract.comp (fromOp.comp Θ)
  have hfromOpCP : IsCompletelyPositive fromOp := by
    dsimp only [fromOp]
    exact isCompletelyPositive_of_starAlgHom
      opEquiv.symm.toStarAlgHom.toNonUnitalStarAlgHom
  refine ⟨Ψ, R.retract_completelyPositive.comp (hfromOpCP.comp hΘcp), ?_, ?_⟩
  · dsimp only [Ψ, LinearMap.comp_apply]
    rw [hΘone]
    change R.retract (opEquiv.symm 1) = 1
    rw [map_one, R.retract_one]
  · intro a
    let c : C := ⟨e a, ⟨a, rfl⟩⟩
    have hΘa : Θ (e a) = Φ c := hΘext c
    dsimp only [Ψ, LinearMap.comp_apply]
    rw [hΘa]
    change R.retract (opEquiv.symm (opEquiv (R.embedding (φ (er.symm c))))) = φ a
    rw [opEquiv.symm_apply_apply, R.retract_embedding]
    congr 1
    apply er.injective
    calc
      er (er.symm c) = c := er.apply_symm_apply c
      _ = er a := by
        apply Subtype.ext
        rfl

/-- Closed universal packaging of the finite-dimensional UCP extension
theorem. -/
def FiniteDimensionalUCPExtension : Prop :=
  ∀ (A : Type u) (B : Type) (D : Type w)
    [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra D]
    [Nontrivial A] [Nontrivial B] [Nontrivial D]
    [FiniteDimensional ℂ D]
    (e : A →⋆ₐ[ℂ] B), Function.Injective e →
    ∀ (φ : A →ₗ[ℂ] D), IsCompletelyPositive φ → φ 1 = 1 →
      ∃ Ψ : B →ₗ[ℂ] D,
        IsCompletelyPositive Ψ ∧ Ψ 1 = 1 ∧ ∀ a : A, Ψ (e a) = φ a

/-- Every finite-dimensional UCP map extends across a faithful unital C-star
inclusion. -/
theorem finiteDimensionalUCPExtension : FiniteDimensionalUCPExtension := by
  intro A B D _ _ _ _ _ _ _ e he φ hφcp hφone
  exact exists_ucp_extension_finiteDimensional e he φ hφcp hφone

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms starAlgEquivRange
#audit_axioms isClosed_starAlgHomRange
#audit_axioms exists_ucp_extension_finiteDimensional
#audit_closed_axioms finiteDimensionalUCPExtension
