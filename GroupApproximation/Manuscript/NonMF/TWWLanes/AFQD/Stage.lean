import GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.Presentation
import GroupApproximation.Analysis.BlackadarKirchbergFiniteDimensionalArvesonExtension
import GroupApproximation.Analysis.MatrixModelFormPositivity
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationData
import GroupApproximation.Meta.AxiomGuard

/-!
# AF algebras: one stage of the matrix model

Lane `nm-tww-04`. Fix an AF presentation `ιₙ : Bₙ → A`, a tracial state `τ` on `A`,
and a stage `n`. This module builds a ucp map `φₙ : A → M_{N}` that

* is multiplicative on the range of `ιₙ`, and
* satisfies `‖τ(ιₙ b) − tr_N(φₙ(ιₙ b))‖ ≤ ‖ιₙ b‖ / (n + 2)`.

## Route

1. `τₙ := τ ∘ ιₙ` is a tracial state on `Bₙ`
   (`TracialState.compStarAlgHom`). Both `A` and `Bₙ` are nontrivial because they carry
   a tracial state.
2. The upstream Statement at `ε = 1/(n+2)` gives a unital ⋆-homomorphism
   `π : Bₙ → M_N` with `|τₙ b − tr_N(π b)| ≤ ε‖b‖`. Testing at `b = 1` rules out
   `N = 0`: then `tr_N = 0`, so `1 ≤ ε < 1`.
3. `ρ := toEuclideanCLM ∘ reindex ∘ π : Bₙ → B(ℓ²(Fin N))` is a unital ⋆-homomorphism,
   so it is completely positive (`isCompletelyPositive_of_starAlgHom`).
4. The finite-dimensional Arveson extension across the injective ⋆-homomorphism `ιₙ`
   (`BlackadarKirchberg.exists_ucp_extension_finiteDimensional`) gives a ucp map
   `Ψ : A → B(ℓ²(Fin N))` with `Ψ ∘ ιₙ = ρ`.
5. `φₙ := matrixOfEuclidean ∘ Ψ` is unital and form-positive
   (`isCompletelyPositiveOnMatrices_matrixOfEuclidean`). Since `φₙ(ιₙ b) = π b`, it is
   multiplicative on the range of `ιₙ`. `ιₙ` is isometric
   (`NonUnitalStarAlgHom.norm_map`), and this turns the trace bound for `π` into the
   stated one.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace AFQD

open CStarExactness Quasidiagonal LocalLifting
open scoped Matrix.Norms.L2Operator

noncomputable section

attribute [local instance] matrixBlockCStarAlgebra multimatrixCStarAlgebra

/-- The finite model on `Fin N`. -/
def finModel (N : ℕ) : FiniteModel := ⟨Fin N, inferInstance, inferInstance⟩

theorem card_finModel (N : ℕ) : Fintype.card (finModel N) = N :=
  Fintype.card_fin N

variable {A : Type} [CStarAlgebra A]

/-- **One stage of the matrix model of an AF algebra.** At stage `n` there is a ucp
matrix map on `A` that is multiplicative on the range of `ιₙ` and reproduces `τ` there
up to `‖ιₙ b‖ / (n + 2)`. -/
theorem exists_stage (h : MultimatrixTraceAmplificationStatement) (P : AFPresentation A)
    (τ : TracialState A) (n : ℕ) :
    ∃ (Y : FiniteModel) (φ : A →ₗ[ℂ] Matrix Y Y ℂ),
      φ 1 = 1 ∧ IsCompletelyPositiveOnMatrices Y ⇑φ ∧
      (∀ b c : Multimatrix (P.blocks n) (P.sizes n),
        φ (P.embed n b * P.embed n c) = φ (P.embed n b) * φ (P.embed n c)) ∧
      ∀ b : Multimatrix (P.blocks n) (P.sizes n),
        ‖τ (P.embed n b) - normTrace Y (φ (P.embed n b))‖ ≤
          1 / ((n : ℝ) + 2) * ‖P.embed n b‖ := by
  classical
  haveI : Nontrivial A := MFRecognition.TensorSynchronization.nontrivial_of_tracialState τ
  haveI : Nontrivial (Multimatrix (P.blocks n) (P.sizes n)) :=
    MFRecognition.TensorSynchronization.nontrivial_of_tracialState
      (τ.compStarAlgHom (P.embed n))
  have hε : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  obtain ⟨N, π, hπ⟩ := h (P.blocks n) (P.sizes n) (τ.compStarAlgHom (P.embed n)) _ hε
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · exfalso
      have hlt : 1 / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have hle : (1 : ℝ) ≤ 1 / ((n : ℝ) + 2) := by
        calc (1 : ℝ) = ‖(τ.compStarAlgHom (P.embed n)) 1
              - Matrix.trace (π 1) / ((0 : ℕ) : ℂ)‖ := by
                rw [Nat.cast_zero, div_zero, sub_zero, TracialState.apply_one, norm_one]
          _ ≤ 1 / ((n : ℝ) + 2) * ‖(1 : Multimatrix (P.blocks n) (P.sizes n))‖ := hπ 1
          _ = 1 / ((n : ℝ) + 2) := by rw [CStarRing.norm_one, mul_one]
      linarith
    · exact hpos
  have hcard : Fintype.card (finModel N) = N := card_finModel N
  haveI : Nonempty (Fin (Fintype.card (finModel N))) := ⟨⟨0, by rw [hcard]; exact hN⟩⟩
  haveI : Nontrivial (EuclideanSpace ℂ (Fin (Fintype.card (finModel N))) →L[ℂ]
      EuclideanSpace ℂ (Fin (Fintype.card (finModel N)))) :=
    (Matrix.toEuclideanCLM (n := Fin (Fintype.card (finModel N))) (𝕜 := ℂ)).injective.nontrivial
  let π' : Multimatrix (P.blocks n) (P.sizes n) →⋆ₐ[ℂ]
      Matrix (finModel N) (finModel N) ℂ := π
  let ρ : Multimatrix (P.blocks n) (P.sizes n) →⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Fin (Fintype.card (finModel N))) →L[ℂ]
        EuclideanSpace ℂ (Fin (Fintype.card (finModel N)))) :=
    (Matrix.toEuclideanCLM (n := Fin (Fintype.card (finModel N))) (𝕜 := ℂ)).toStarAlgHom.comp
      ((matrixReindexStarAlgEquiv (enum (finModel N))).toStarAlgHom.comp π')
  obtain ⟨Ψ, hΨcp, hΨone, hΨext⟩ :=
    BlackadarKirchberg.exists_ucp_extension_finiteDimensional (P.embed n) (P.injective n)
      (ρ.toNonUnitalStarAlgHom : Multimatrix (P.blocks n) (P.sizes n) →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin (Fintype.card (finModel N))) →L[ℂ]
          EuclideanSpace ℂ (Fin (Fintype.card (finModel N)))))
      (isCompletelyPositive_of_starAlgHom ρ.toNonUnitalStarAlgHom) (map_one ρ)
  have hval : ∀ b : Multimatrix (P.blocks n) (P.sizes n),
      (matrixOfEuclidean (finModel N)).comp Ψ (P.embed n b) = π' b := by
    intro b
    rw [LinearMap.comp_apply, hΨext b]
    exact matrixOfEuclidean_euclideanize (finModel N) (π' b)
  refine ⟨finModel N, (matrixOfEuclidean (finModel N)).comp Ψ, ?_,
    isCompletelyPositiveOnMatrices_matrixOfEuclidean (finModel N) Ψ hΨcp, ?_, ?_⟩
  · rw [LinearMap.comp_apply, hΨone, matrixOfEuclidean_one]
  · intro b c
    rw [← map_mul (P.embed n) b c, hval, hval, hval]
    exact map_mul π' b c
  · intro b
    have hnorm : ‖P.embed n b‖ = ‖b‖ :=
      NonUnitalStarAlgHom.norm_map (P.embed n) (P.injective n) b
    have htr : normTrace (finModel N) ((matrixOfEuclidean (finModel N)).comp Ψ
        (P.embed n b)) = Matrix.trace (π b) / (N : ℂ) := by
      rw [hval b]
      show Matrix.trace (π b) / ((Fintype.card (finModel N) : ℕ) : ℂ) = _
      rw [hcard]
    rw [htr, hnorm]
    exact hπ b

end

end AFQD
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.finModel
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.card_finModel
#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.AFQD.exists_stage
