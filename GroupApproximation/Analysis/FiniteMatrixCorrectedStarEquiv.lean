import GroupApproximation.Analysis.FiniteMatrixPositiveSquareRootUnit
import GroupApproximation.Analysis.FiniteMatrixTransportedInvolution

/-!
# Correcting a finite matrix algebra equivalence to preserve star

The positive invertible square root of the transported-star conjugator gives
the final similarity correction.  Conjugation by its inverse intertwines the
transported involution with the ordinary adjoint.
-/

namespace GroupApproximation
namespace BlackadarKirchberg

noncomputable section

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

end

end BlackadarKirchberg
end GroupApproximation

open GroupApproximation.BlackadarKirchberg

#audit_axioms exists_correctedStarAlgEquiv_to_moduleEnd
