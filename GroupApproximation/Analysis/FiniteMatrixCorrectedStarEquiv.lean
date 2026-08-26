import GroupApproximation.Analysis.FiniteMatrixPositiveSquareRootUnit
import GroupApproximation.Analysis.FiniteMatrixTransportedInvolution
import GroupApproximation.Analysis.BlackadarKirchbergStarEquivTransport

/-!
# Correcting a finite matrix algebra equivalence to preserve star

The positive invertible square root of the transported-star conjugator gives
the final similarity correction.  Conjugation by its inverse intertwines the
transported involution with the ordinary adjoint.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

noncomputable section

open scoped Matrix.Norms.L2Operator

local instance matrixBlockCStarAlgebraForCorrected
    (Z : Type*) [Fintype Z] [DecidableEq Z] [Nonempty Z] :
    CStarAlgebra (Matrix Z Z ℂ) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

local instance boundedMatrixSequenceCStarAlgebraForCorrected
    (X : ℕ → Type*) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)] : CStarAlgebra (BoundedMatrixSequence X) where
  toNormedRing := inferInstance
  toStarRing := inferInstance
  toCompleteSpace := inferInstance
  toCStarRing := inferInstance
  toNormedAlgebra := inferInstance
  toStarModule := inferInstance

/-- Every complex-algebra equivalence from a C-star algebra onto the
endomorphisms of a nonzero finite-dimensional Hilbert space can be corrected
by an inner automorphism to a star-algebra equivalence. -/
theorem exists_correctedStarAlgEquiv_to_moduleEnd
    {D V : Type*} [CStarAlgebra D] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (e : D ≃ₐ[ℂ] Module.End ℂ V) :
    Nonempty (D ≃⋆ₐ[ℂ] Module.End ℂ V) := by
  letI := FiniteDimensional.complete ℂ V
  obtain ⟨S, hSconj, hSadj⟩ :=
    exists_selfAdjoint_conjugator_for_transportedInvolution e
  have hSsymm : S.toLinearMap.IsSymmetric := by
    intro x y
    calc
      inner ℂ (S x) y = inner ℂ (adjointLinearEquiv S x) y := by rw [hSadj]
      _ = inner ℂ x (S y) :=
        LinearMap.adjoint_inner_left S.toLinearMap y x
  have hSaniso : ∀ w : V, w ≠ 0 → inner ℂ w (S.symm w) ≠ 0 :=
    fun w hw ↦ conjugator_inverseForm_anisotropic e S hSconj hw
  obtain ⟨sign, A, R, hsign, hA, _hApos, hRself, hRsquare, hRunit⟩ :=
    exists_positive_unit_squareRoot_of_inverseForm_anisotropic S hSsymm hSaniso
  have hRbij : Function.Bijective R :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hRunit
  let U : V ≃ₗ[ℂ] V := LinearEquiv.ofBijective R.toLinearMap hRbij
  have hUsymm : U.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℂ (R x) y = inner ℂ x (R y)
    exact hRself.isSymmetric x y
  have hUadj : adjointLinearEquiv U = U := by
    apply LinearEquiv.ext
    intro x
    apply ext_inner_right ℂ
    intro y
    calc
      inner ℂ (adjointLinearEquiv U x) y = inner ℂ x (U y) :=
        LinearMap.adjoint_inner_left U.toLinearMap y x
      _ = inner ℂ (U x) y := (hUsymm x y).symm
  have hUtwo (x : V) :
      (U.trans U) x = (sign : ℂ) • S x := by
    have hRpoint := congrArg (fun T : V →L[ℂ] V ↦ T x) hRsquare
    change R (R x) = A x at hRpoint
    have hApoint := LinearMap.congr_fun hA x
    calc
      (U.trans U) x = R (R x) := by rfl
      _ = A x := hRpoint
      _ = (sign : ℂ) • S x := hApoint
  have hconjSquare :
      (U.trans U).conjAlgEquiv ℂ = S.conjAlgEquiv ℂ := by
    rcases hsign with rfl | rfl
    · apply (LinearEquiv.conjAlgEquiv_ext_iff' (U.trans U) S).mpr
      refine ⟨1, ?_⟩
      apply LinearEquiv.ext
      intro x
      simpa using hUtwo x
    · apply (LinearEquiv.conjAlgEquiv_ext_iff' (U.trans U) S).mpr
      refine ⟨(-1 : ℂˣ), ?_⟩
      apply LinearEquiv.ext
      intro x
      simpa using hUtwo x
  have hcancel (x : Module.End ℂ V) :
      U.symm.conjAlgEquiv ℂ (S.conjAlgEquiv ℂ x) =
        U.conjAlgEquiv ℂ x := by
    rw [← hconjSquare]
    ext v
    simp [LinearEquiv.conjAlgEquiv_apply]
  have hintertwine (x : Module.End ℂ V) :
      U.symm.conjAlgEquiv ℂ (transportedInvolution e x) =
        star (U.symm.conjAlgEquiv ℂ x) := by
    calc
      U.symm.conjAlgEquiv ℂ (transportedInvolution e x) =
          U.symm.conjAlgEquiv ℂ (S.conjAlgEquiv ℂ (star x)) := by
            rw [transportedInvolution_eq_automorphism_star, ← hSconj]
      _ = U.conjAlgEquiv ℂ (star x) := hcancel (star x)
      _ = (adjointLinearEquiv U).conjAlgEquiv ℂ (star x) := by rw [hUadj]
      _ = star (U.symm.conjAlgEquiv ℂ x) :=
        (star_conjAlgEquiv_apply U.symm x).symm
  let fAlg : D ≃ₐ[ℂ] Module.End ℂ V :=
    e.trans (U.symm.conjAlgEquiv ℂ)
  refine ⟨StarAlgEquiv.ofAlgEquiv fAlg ?_⟩
  intro d
  change U.symm.conjAlgEquiv ℂ (e (star d)) =
    star (U.symm.conjAlgEquiv ℂ (e d))
  have heStar : e (star d) = transportedInvolution e (e d) := by
    simp [transportedInvolution]
  rw [heStar]
  exact hintertwine (e d)

/-! ## The concrete full-matrix form -/

/-- On a finite-dimensional Hilbert space, passing from algebraic
endomorphisms to continuous endomorphisms is a star-algebra equivalence. -/
def moduleEndToContinuousStarAlgEquiv
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] :
    Module.End ℂ V ≃⋆ₐ[ℂ] (V →L[ℂ] V) := by
  letI := FiniteDimensional.complete ℂ V
  exact StarAlgEquiv.ofAlgEquiv (Module.End.toContinuousLinearMap V)
    LinearMap.adjoint_toContinuousLinearMap

/-- Every complex-algebra equivalence from a C-star algebra onto a nonzero
full matrix algebra can be corrected by an inner automorphism to preserve
the involution.  This is the concrete-matrix version of
`exists_correctedStarAlgEquiv_to_moduleEnd`. -/
theorem exists_correctedStarAlgEquiv_to_matrix
    {D : Type*} [CStarAlgebra D] {k : ℕ} [Nonempty (Fin k)]
    (e : D ≃ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ) :
    Nonempty (D ≃⋆ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ) := by
  let V := EuclideanSpace ℂ (Fin k)
  let matrixToEnd : Matrix (Fin k) (Fin k) ℂ ≃⋆ₐ[ℂ] Module.End ℂ V :=
    (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ)).trans
      (moduleEndToContinuousStarAlgEquiv V).symm
  let eEnd : D ≃ₐ[ℂ] Module.End ℂ V := e.trans matrixToEnd.toAlgEquiv
  obtain ⟨corrected⟩ := exists_correctedStarAlgEquiv_to_moduleEnd eEnd
  exact ⟨corrected.trans matrixToEnd.symm⟩

/-- Every finite-dimensional simple complex C-star algebra is
star-isomorphic to a nonzero full matrix algebra.  Artin--Wedderburn supplies
the algebra equivalence and `exists_correctedStarAlgEquiv_to_matrix` corrects
its involution. -/
theorem exists_starAlgEquiv_matrix_of_finiteDimensional_simpleCStar
    (D : Type*) [CStarAlgebra D] [FiniteDimensional ℂ D] [IsSimpleRing D] :
    ∃ (k : ℕ) (hk : Nonempty (Fin k)),
      letI : Nonempty (Fin k) := hk
      Nonempty (D ≃⋆ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ) := by
  obtain ⟨k, hk, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed ℂ D
  have hk' : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (NeZero.pos k)
  exact ⟨k, hk', exists_correctedStarAlgEquiv_to_matrix e⟩

/-- A completely positive contraction from a C-star algebra algebraically
equivalent to one nonzero full matrix block has an exact completely positive
contractive lift through the concrete matrix corona.  No star-preserving
decomposition is assumed: it is produced by
`exists_correctedStarAlgEquiv_to_matrix`. -/
theorem exists_completelyPositiveContractive_lift_of_algEquiv_matrix
    {D : Type*} [CStarAlgebra D] {k : ℕ} [Nonempty (Fin k)]
    {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)]
    (e : D ≃ₐ[ℂ] Matrix (Fin k) (Fin k) ℂ)
    (f : D →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : CStarExactness.IsCompletelyPositive f)
    (hcontract : ∀ x, ‖f x‖ ≤ ‖x‖) :
    ∃ lift : D →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive lift ∧
      (∀ x, ‖lift x‖ ≤ ‖x‖) ∧
      ∀ x, normMatrixCStarCoronaQuotient X (lift x) = f x := by
  obtain ⟨eStar⟩ := exists_correctedStarAlgEquiv_to_matrix e
  let pushed : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] NormMatrixCStarCorona X :=
    f.comp (starAlgEquivLinearMap eStar.symm)
  have hpushed : CStarExactness.IsCompletelyPositive pushed := by
    change CStarExactness.IsCompletelyPositive
      (f.comp (starAlgEquivLinearMap eStar.symm))
    exact isCompletelyPositive_comp_starAlgEquiv eStar.symm f hf
  have hpushedContract : ∀ y, ‖pushed y‖ ≤ ‖y‖ := by
    intro y
    exact (hcontract (eStar.symm y)).trans_eq (StarAlgEquiv.norm_map eStar.symm y)
  obtain ⟨matrixLift, hmatrixCP, hmatrixContract, hmatrixQuot⟩ :=
    exists_completelyPositiveContractive_matrix_lift X pushed hpushed
      hpushedContract
  let lift : D →ₗ[ℂ] BoundedMatrixSequence X :=
    matrixLift.comp (starAlgEquivLinearMap eStar)
  refine ⟨lift, ?_, ?_, ?_⟩
  · exact isCompletelyPositive_comp_starAlgEquiv eStar matrixLift hmatrixCP
  · intro x
    exact (hmatrixContract (eStar x)).trans_eq (StarAlgEquiv.norm_map eStar x)
  · intro x
    exact (hmatrixQuot (eStar x)).trans (congrArg f (eStar.symm_apply_apply x))

/-- Every completely positive contraction from a finite-dimensional simple
complex C-star algebra to a concrete matrix corona has an exact completely
positive contractive lift. -/
theorem exists_completelyPositiveContractive_lift_of_finiteDimensional_simpleCStar
    {D : Type*} [CStarAlgebra D] [FiniteDimensional ℂ D] [IsSimpleRing D]
    {X : ℕ → Type*} [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    [∀ n, Nonempty (X n)]
    (f : D →ₗ[ℂ] NormMatrixCStarCorona X)
    (hf : CStarExactness.IsCompletelyPositive f)
    (hcontract : ∀ x, ‖f x‖ ≤ ‖x‖) :
    ∃ lift : D →ₗ[ℂ] BoundedMatrixSequence X,
      CStarExactness.IsCompletelyPositive lift ∧
      (∀ x, ‖lift x‖ ≤ ‖x‖) ∧
      ∀ x, normMatrixCStarCoronaQuotient X (lift x) = f x := by
  obtain ⟨k, hk, ⟨e⟩⟩ :=
    exists_starAlgEquiv_matrix_of_finiteDimensional_simpleCStar D
  letI : Nonempty (Fin k) := hk
  exact exists_completelyPositiveContractive_lift_of_algEquiv_matrix
    e.toAlgEquiv f hf hcontract

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_correctedStarAlgEquiv_to_moduleEnd
#audit_axioms moduleEndToContinuousStarAlgEquiv
#audit_axioms exists_correctedStarAlgEquiv_to_matrix
#audit_axioms exists_starAlgEquiv_matrix_of_finiteDimensional_simpleCStar
#audit_axioms exists_completelyPositiveContractive_lift_of_algEquiv_matrix
#audit_axioms exists_completelyPositiveContractive_lift_of_finiteDimensional_simpleCStar
