import GroupApproximation.Analysis.NaturalMatrixCoordinateEquiv
import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.IntrinsicCompressionMFRadical
import GroupApproximation.Sofic.KazhdanAsymptoticCommutant

/-!
# Exact manuscript form of Kazhdan transport

This file exposes the forward transport theorem with exactly the objects used
in the manuscript: natural matrix dimensions, raw unitary-valued
operator-norm almost representations, and normalized Hilbert--Schmidt
commutators.  The reusable proof remains in
`KazhdanAsymptoticCommutant.transport`.
-/

namespace GroupApproximation
namespace KazhdanAsymptoticCommutant

open Matrix
open scoped Matrix.Norms.L2Operator

universe w

variable {H : Type} [Group H]

/-- Convergence of a raw matrix commutator to zero in normalized
Hilbert--Schmidt norm, written in the natural coordinates `M_{d n}`. -/
def NaturalHSCommutatorVanishing
    (d : ℕ → ℕ)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (x : ∀ n, Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ)
    (g : H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
    Real.sqrt (hsNormSq (naturalFiniteModel (d n))
      (x n * U n g - U n g * x n)) ≤ ε

/-- **Kazhdan transport in the exact manuscript coordinates.**  No lamp or
centralizer datum is an input: the proof internally applies the general
compression theorem with the harmless root `1`. -/
theorem manuscriptKazhdanTransport
    {Γ : Type} [Group Γ]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H) (s : H)
    (hs : ∀ γ : Γ, ∃ δ : Γ,
      s * iota γ * s⁻¹ = iota δ)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (U : ∀ n, H → Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ)
    (hU : ∀ g h : H, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N,
      ‖(U n (g * h) : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) -
        (U n g : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ) * U n h‖ ≤ ε)
    (x : ∀ n, Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ)
    (hbound : ∃ M : ℝ, 0 ≤ M ∧ ∀ n, ‖x n‖ ≤ M)
    (hx : ∀ γ : Γ, NaturalHSCommutatorVanishing d U x (iota γ)) :
    ∀ γ : Γ, NaturalHSCommutatorVanishing d U (fun n ↦
      (U n s : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ) * x n *
        (U n s : Matrix (naturalFiniteModel (d n))
          (naturalFiniteModel (d n)) ℂ)ᴴ) (iota γ) := by
  let B : OpAlmostRepresentation H := {
    model := fun n ↦ naturalFiniteModel (d n)
    modelNonempty := fun n ↦ by
      simpa using hd n
    map := U
    asymptoticallyMultiplicative := hU
  }
  let C : KazhdanCompressionCore Γ H := {
    iota := iota
    t := s
    c := 1
    kazhdan := hasKazhdanPropertyT_iff_textbook.mpr hT
    compresses := hs
    comm_c γ := Commute.one_left (iota γ)
  }
  have hx_sq : IsAsymptoticCommutant B C x := by
    intro γ ε hε
    obtain ⟨N, hN⟩ := hx γ (Real.sqrt ε) (Real.sqrt_pos.2 hε)
    refine ⟨N, fun n hn ↦ ?_⟩
    let V : Matrix (naturalFiniteModel (d n))
        (naturalFiniteModel (d n)) ℂ := U n (iota γ)
    have hV : V ∈ Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ :=
      (U n (iota γ)).2
    have hcomm := hN n hn
    have hcommSq : hsNormSq (naturalFiniteModel (d n))
        (x n * V - V * x n) ≤ ε := by
      calc
        hsNormSq (naturalFiniteModel (d n)) (x n * V - V * x n) =
            (Real.sqrt (hsNormSq (naturalFiniteModel (d n))
              (x n * V - V * x n))) ^ 2 :=
          (Real.sq_sqrt (hsNormSq_nonneg _ _)).symm
        _ ≤ (Real.sqrt ε) ^ 2 :=
          (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).2 hcomm
        _ = ε := Real.sq_sqrt hε.le
    have hVVstar : V * Vᴴ = 1 := Unitary.mul_star_self_of_mem hV
    have hfactor : x n - V * x n * Vᴴ = (x n * V - V * x n) * Vᴴ := by
      noncomm_ring [hVVstar]
    change hsNormSq (naturalFiniteModel (d n)) (x n - V * x n * Vᴴ) ≤ ε
    rw [hfactor,
      hsNormSq_mul_right _
        (MarkedCompressionVectorChain.conjTranspose_mem_unitaryGroup hV)]
    exact hcommSq
  have hbound' : IsUniformlyBounded B x := hbound
  have hy_sq := transport B C x hx_sq hbound'
  intro γ ε hε
  obtain ⟨N, hN⟩ := hy_sq γ (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  let S : Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ := U n s
  let V : Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ := U n (iota γ)
  let y : Matrix (naturalFiniteModel (d n))
      (naturalFiniteModel (d n)) ℂ := S * x n * Sᴴ
  have hV : V ∈ Matrix.unitaryGroup (naturalFiniteModel (d n)) ℂ :=
    (U n (iota γ)).2
  have hVstarV : Vᴴ * V = 1 := Unitary.star_mul_self_of_mem hV
  have hfactor : y * V - V * y = (y - V * y * Vᴴ) * V := by
    noncomm_ring [hVstarV]
  have hdisp : hsNormSq (naturalFiniteModel (d n))
      (y - V * y * Vᴴ) ≤ ε ^ 2 := by
    simpa [B, C, S, V, y] using hN n hn
  have hcommSq : hsNormSq (naturalFiniteModel (d n))
      (y * V - V * y) ≤ ε ^ 2 := by
    rw [hfactor, hsNormSq_mul_right _ hV]
    exact hdisp
  have hsqrt := Real.sqrt_le_sqrt hcommSq
  simpa [NaturalHSCommutatorVanishing, S, V, y,
    Real.sqrt_sq hε.le] using hsqrt

/-- **The intrinsic compression radical in the exact manuscript corona.**
For a countable ambient group, every finite normal subgroup of the intrinsic
compression--centralizer defect of a Kazhdan image lies in the literal
natural-dimension C-star-corona radical.  The second conjunct spells out the
equivalent kernel statement for every printed norm-matrix corona. -/
theorem manuscriptCompressionRadical
    {Γ H : Type} [Group Γ] [Group H] [Countable H]
    (hT : HasKazhdanPropertyTComplex.{0, w} Γ)
    (iota : Γ →* H)
    (F : Subgroup H) [Finite F] [F.Normal]
    (hF : F ≤ compressionCentralizerDefect iota.range) :
    F ≤ manuscriptCoronaMFResidual H ∧
      ∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ rho : H →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          F ≤ rho.ker := by
  have hnorm : F ≤ normMFResidual H :=
    finiteNormal_le_normMFResidual_of_le_compressionCentralizerDefect
      iota (hasKazhdanPropertyT_iff_textbook.mpr hT) F hF
  have hres : F ≤ manuscriptCoronaMFResidual H := by
    rw [manuscriptCoronaMFResidual_eq_coronaMFResidual,
      coronaMFResidual_eq_normMFResidual]
    exact hnorm
  refine ⟨hres, ?_⟩
  intro d hd
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  intro rho f hf
  exact MonoidHom.mem_ker.mpr
    ((mem_manuscriptCoronaMFResidual_iff.mp (hres hf)) d hd rho)

end KazhdanAsymptoticCommutant
end GroupApproximation
