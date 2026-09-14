import GroupApproximation.Analysis.HyperfiniteStageCorner
import GroupApproximation.Analysis.TracialUltrapowerTrace
import GroupApproximation.Analysis.TracialUltraproductCStar
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The tracial matrix ultraproduct embeds in `𝓡^ω`

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93): "`L(G)` embeds in `𝓡^ω`".  oa-mcduff builds `L(G) → ∏_ω M_k` for a
hyperlinear `G`; this module supplies the unital trace-preserving `⋆`-homomorphism
`∏_ω M_k → 𝓡^ω` it is composed with.

* `hyperfiniteTracialVector`: `δ₁` is a tracial vector for `𝓡`; `HyperfiniteUltrapower ω` is `𝓡^ω`.
* At coordinate `n` with `k = |X n|`, the stage is `j = k (n+1)` and the multiplicity `r = ⌊2^j/k⌋`.
  So `k r ≤ 2^j` gives a corner, and the trace factor `stageFactor n = r k / 2^j` satisfies
  `1 − 1/(n+1) ≤ stageFactor n ≤ 1`.
* `seqMap`: the coordinatewise stage-corner maps on bounded matrix sequences.  They are exactly
  multiplicative, additive and `⋆`-preserving, bounded by contractivity, and send `‖·‖₂`-null
  sequences to `‖·‖₂`-null sequences.  Their unit defect has 2-norm `√(1 − stageFactor n) → 0`.
* `matrixUltraproductToHyperfiniteUltrapower X ω hω`: the induced unital `⋆`-algebra homomorphism
  `TracialMatrixQuotient X ω →⋆ₐ[ℂ] HyperfiniteUltrapower ω`, for any ultrafilter `ω ≤ cofinite`.
* `ultratrace_matrixUltraproductToHyperfiniteUltrapower`: it preserves the ultratraces.
-/

namespace GroupApproximation
namespace Hyperfinite

open Filter TwistedGroupVonNeumann ReducedGroupCStarTrace MatrixUnits TracialUltrapower
open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

/-! ## The tracial vector of `𝓡` -/

/-- `δ₁` is a tracial vector for `𝓡`. -/
def hyperfiniteTracialVector : TracialVector hyperfiniteFactor where
  vec := deltaOne PauliGroup
  norm_vec := GroupVonNeumann.norm_deltaOne PauliGroup
  tracial T hT S hS := by
    rw [GroupVonNeumann.inner_deltaOne_left PauliGroup, GroupVonNeumann.inner_deltaOne_left PauliGroup]
    exact coefficient_mul_comm pauliCocycle pauliCocycle_isSignCocycle hT hS

/-- **The tracial ultrapower `𝓡^ω`.** -/
abbrev HyperfiniteUltrapower (ω : Ultrafilter ℕ) : Type :=
  Ultrapower hyperfiniteTracialVector ω

/-- **The ultratrace of `𝓡^ω`.** -/
abbrev hyperfiniteUltratrace (ω : Ultrafilter ℕ) : HyperfiniteUltrapower ω →+ ℂ :=
  ultratrace hyperfiniteTracialVector ω

/-! ## Stage choices -/

variable (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]

/-- The Pauli stage used at coordinate `n`: `j = k (n+1)` for `k = |X n|`. -/
def stageLevel (n : ℕ) : ℕ :=
  Fintype.card (X n) * (n + 1)

/-- The multiplicity at coordinate `n`: `r = ⌊2^j / k⌋`. -/
def stageMult (n : ℕ) : ℕ :=
  2 ^ stageLevel X n / Fintype.card (X n)

theorem card_mul_stageMult_le (n : ℕ) :
    Fintype.card (X n) * stageMult X n ≤ 2 ^ stageLevel X n := by
  rw [mul_comm]
  exact Nat.div_mul_le_self _ _

theorem stageEmbedding_nonempty (n : ℕ) :
    Nonempty (X n × Fin (stageMult X n) ↪ StageIdx (stageLevel X n)) :=
  nonempty_cornerEmbedding (by rw [card_stageIdx]; exact card_mul_stageMult_le X n)

/-- A chosen corner at coordinate `n`. -/
def stageEmbedding (n : ℕ) : X n × Fin (stageMult X n) ↪ StageIdx (stageLevel X n) :=
  Classical.choice (stageEmbedding_nonempty X n)

/-- **The trace factor** `r k / 2^j` at coordinate `n`. -/
def stageFactor (n : ℕ) : ℝ :=
  ((Fintype.card (X n) * stageMult X n : ℕ) : ℝ) / 2 ^ stageLevel X n

theorem stageFactor_complex (n : ℕ) :
    ((2 : ℂ) ^ stageLevel X n)⁻¹ * ((stageMult X n : ℂ) * Fintype.card (X n)) =
      ((stageFactor X n : ℝ) : ℂ) := by
  simp only [stageFactor]
  push_cast
  ring

theorem stageFactor_nonneg (n : ℕ) : 0 ≤ stageFactor X n := by
  unfold stageFactor
  positivity

theorem stageFactor_le_one (n : ℕ) : stageFactor X n ≤ 1 := by
  have hpow : (0 : ℝ) < 2 ^ stageLevel X n := by positivity
  rw [stageFactor, div_le_one hpow]
  exact_mod_cast card_mul_stageMult_le X n

theorem one_sub_stageFactor_le (n : ℕ) : 1 - stageFactor X n ≤ 1 / ((n : ℝ) + 1) := by
  have hK : 0 < Fintype.card (X n) := Fintype.card_pos
  have h1 : 2 ^ stageLevel X n < Fintype.card (X n) * stageMult X n + Fintype.card (X n) := by
    have h := Nat.lt_div_mul_add (a := 2 ^ stageLevel X n) hK
    rw [stageMult, mul_comm (Fintype.card (X n))]
    exact h
  have h2 : Fintype.card (X n) * (n + 1) < 2 ^ stageLevel X n :=
    (Nat.lt_two_pow_self : stageLevel X n < 2 ^ stageLevel X n)
  have hpow : (0 : ℝ) < 2 ^ stageLevel X n := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1' : (2 : ℝ) ^ stageLevel X n <
      (Fintype.card (X n) : ℝ) * stageMult X n + Fintype.card (X n) := by
    exact_mod_cast h1
  have h2' : (Fintype.card (X n) : ℝ) * ((n : ℝ) + 1) < 2 ^ stageLevel X n := by
    exact_mod_cast h2
  have h3 : ((2 : ℝ) ^ stageLevel X n - Fintype.card (X n) * stageMult X n) * ((n : ℝ) + 1) ≤
      (Fintype.card (X n) : ℝ) * ((n : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hn.le
  have hkey : (1 - stageFactor X n) * ((n : ℝ) + 1) ≤ 1 := by
    have hsf : 1 - stageFactor X n =
        ((2 : ℝ) ^ stageLevel X n - Fintype.card (X n) * stageMult X n) / 2 ^ stageLevel X n := by
      rw [stageFactor]
      push_cast
      field_simp
    rw [hsf, div_mul_eq_mul_div, div_le_one hpow]
    linarith
  rw [le_div_iff₀ hn]
  exact hkey

theorem tendsto_stageFactor : Tendsto (stageFactor X) atTop (nhds 1) := by
  have hsub : Tendsto (fun n ↦ 1 - stageFactor X n) atTop (nhds 0) :=
    squeeze_zero (fun n ↦ sub_nonneg.mpr (stageFactor_le_one X n)) (one_sub_stageFactor_le X)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hsub
  rw [sub_zero] at h
  exact h.congr fun n ↦ sub_sub_cancel 1 (stageFactor X n)

theorem norm_stageCorner_deltaOne_sq' (n : ℕ) (A : Matrix (X n) (X n) ℂ) :
    ‖stageCorner (stageEmbedding X n) A (deltaOne PauliGroup)‖ ^ 2 =
      stageFactor X n * hsNormSq (X n) A := by
  apply Complex.ofReal_injective
  rw [norm_stageCorner_deltaOne_sq, stageFactor_complex, Complex.ofReal_mul]

theorem norm_one_sub_stageCorner_one_deltaOne_sq' (n : ℕ) :
    ‖(1 - stageCorner (stageEmbedding X n) 1) (deltaOne PauliGroup)‖ ^ 2 =
      1 - stageFactor X n := by
  apply Complex.ofReal_injective
  rw [norm_one_sub_stageCorner_one_deltaOne_sq, stageFactor_complex, Complex.ofReal_sub,
    Complex.ofReal_one]

/-! ## The coordinatewise map -/

/-- The coordinatewise stage-corner maps on bounded matrix sequences. -/
def seqMap (a : TracialUltraproduct.ModelBoundedSequence X) : boundedSeq hyperfiniteFactor :=
  ⟨fun n ↦ stageCorner (stageEmbedding X n) (a n), fun n ↦ stageCorner_mem _ _, ‖a‖,
    fun n ↦ (norm_stageCorner_le _ _).trans (boundedMatrixSequence_coord_norm_le (fun n ↦ X n) a n)⟩

theorem seqMap_apply (a : TracialUltraproduct.ModelBoundedSequence X) (n : ℕ) :
    (seqMap X a : ℕ → (GroupHilbert PauliGroup →L[ℂ] GroupHilbert PauliGroup)) n =
      stageCorner (stageEmbedding X n) (a n) :=
  rfl

theorem seqMap_mul (a b : TracialUltraproduct.ModelBoundedSequence X) :
    seqMap X (a * b) = seqMap X a * seqMap X b := by
  apply Subtype.ext
  funext n
  exact map_mul (stageCorner (stageEmbedding X n)) (a n) (b n)

theorem seqMap_add (a b : TracialUltraproduct.ModelBoundedSequence X) :
    seqMap X (a + b) = seqMap X a + seqMap X b := by
  apply Subtype.ext
  funext n
  exact map_add (stageCorner (stageEmbedding X n)) (a n) (b n)

theorem seqMap_zero : seqMap X 0 = 0 := by
  apply Subtype.ext
  funext n
  exact map_zero (stageCorner (stageEmbedding X n))

theorem seqMap_star (a : TracialUltraproduct.ModelBoundedSequence X) :
    seqMap X (star a) = star (seqMap X a) := by
  apply Subtype.ext
  funext n
  exact map_star (stageCorner (stageEmbedding X n)) (a n)

theorem seqMap_smul (c : ℂ) (a : TracialUltraproduct.ModelBoundedSequence X) :
    seqMap X (c • a) = c • seqMap X a := by
  apply Subtype.ext
  funext n
  exact map_smul (stageCorner (stageEmbedding X n)) c (a n)

/-- **Null sequences go to null sequences.** -/
theorem isNull_seqMap (ω : Ultrafilter ℕ) {a : TracialUltraproduct.ModelBoundedSequence X}
    (ha : TracialUltraproduct.IsHilbertSchmidtNull X (ω : Filter ℕ) a) :
    IsNull hyperfiniteTracialVector ω (seqMap X a) := by
  rw [TracialUltraproduct.isHilbertSchmidtNull_iff_sq] at ha
  have hsq : Tendsto (fun n ↦ ‖stageCorner (stageEmbedding X n) (a n) (deltaOne PauliGroup)‖ ^ 2)
      (ω : Filter ℕ) (nhds 0) := by
    refine squeeze_zero (fun n ↦ sq_nonneg _) (fun n ↦ ?_) ha
    rw [norm_stageCorner_deltaOne_sq']
    exact mul_le_of_le_one_left (hsNormSq_nonneg _ _) (stageFactor_le_one X n)
  have hsqrt := hsq.sqrt
  rw [Real.sqrt_zero] at hsqrt
  exact Filter.Tendsto.congr (fun n ↦ Real.sqrt_sq (norm_nonneg _)) hsqrt

/-- **The unit defect is null.** -/
theorem isNull_seqMap_one_sub_one (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    IsNull hyperfiniteTracialVector ω (seqMap X 1 - 1) := by
  have hf : Tendsto (stageFactor X) (ω : Filter ℕ) (nhds 1) :=
    (tendsto_stageFactor X).mono_left (hω.trans Nat.cofinite_eq_atTop.le)
  have hsub : Tendsto (fun n ↦ 1 - stageFactor X n) (ω : Filter ℕ) (nhds 0) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hf
    rwa [sub_self] at h
  have hsq : Tendsto (fun n ↦ ‖(1 - stageCorner (stageEmbedding X n) 1) (deltaOne PauliGroup)‖ ^ 2)
      (ω : Filter ℕ) (nhds 0) :=
    hsub.congr fun n ↦ (norm_one_sub_stageCorner_one_deltaOne_sq' X n).symm
  have hsqrt := hsq.sqrt
  rw [Real.sqrt_zero] at hsqrt
  refine Filter.Tendsto.congr (fun n ↦ ?_) hsqrt
  rw [Real.sqrt_sq (norm_nonneg _)]
  show ‖(1 - stageCorner (stageEmbedding X n) 1) (deltaOne PauliGroup)‖ =
    ‖(stageCorner (stageEmbedding X n) 1 - 1) (deltaOne PauliGroup)‖
  rw [← neg_sub, neg_apply, norm_neg]

/-! ## The homomorphism -/

variable (ω : Ultrafilter ℕ)

/-- The coordinatewise map followed by the quotient map, as a unital ring homomorphism. -/
def liftRingHom (hω : (ω : Filter ℕ) ≤ cofinite) :
    TracialUltraproduct.ModelBoundedSequence X →+* HyperfiniteUltrapower ω where
  toFun a := mk hyperfiniteTracialVector ω (seqMap X a)
  map_one' := by
    rw [← map_one (mk hyperfiniteTracialVector ω), ← sub_eq_zero, ← map_sub, mk_eq_zero_iff]
    exact isNull_seqMap_one_sub_one X ω hω
  map_mul' a b := by
    rw [seqMap_mul, map_mul]
  map_zero' := by
    rw [seqMap_zero, map_zero]
  map_add' a b := by
    rw [seqMap_add, map_add]

/-- The ring homomorphism on the tracial matrix ultraproduct. -/
def matrixUltraproductRingHom (hω : (ω : Filter ℕ) ≤ cofinite) :
    TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ) →+* HyperfiniteUltrapower ω :=
  Ideal.Quotient.lift (TracialUltraproduct.hilbertSchmidtNullIdeal X (ω : Filter ℕ))
    (liftRingHom X ω hω) fun a ha ↦ by
      show mk hyperfiniteTracialVector ω (seqMap X a) = 0
      rw [mk_eq_zero_iff]
      exact isNull_seqMap X ω ha

theorem matrixUltraproductRingHom_mk (hω : (ω : Filter ℕ) ≤ cofinite)
    (a : TracialUltraproduct.ModelBoundedSequence X) :
    matrixUltraproductRingHom X ω hω (TracialUltraproduct.tracialMatrixQuotientMk X (ω : Filter ℕ) a) =
      mk hyperfiniteTracialVector ω (seqMap X a) :=
  Ideal.Quotient.lift_mk _ _ _

/-- **The unital `⋆`-algebra homomorphism `∏_ω M_k → 𝓡^ω`.** -/
def matrixUltraproductToHyperfiniteUltrapower (hω : (ω : Filter ℕ) ≤ cofinite) :
    TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ) →⋆ₐ[ℂ] HyperfiniteUltrapower ω where
  toRingHom := matrixUltraproductRingHom X ω hω
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    have h1 : (c • 1 : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)) =
        TracialUltraproduct.tracialMatrixQuotientMk X (ω : Filter ℕ) (c • 1) := by
      rw [← map_one (TracialUltraproduct.tracialMatrixQuotientMk X (ω : Filter ℕ))]
      rfl
    show matrixUltraproductRingHom X ω hω (c • 1) = c • 1
    rw [h1, matrixUltraproductRingHom_mk, seqMap_smul, mk_smul]
    congr 1
    rw [← matrixUltraproductRingHom_mk X ω hω, map_one, map_one]
  map_star' x := by
    obtain ⟨a, rfl⟩ := TracialUltraproduct.tracialMatrixQuotientMk_surjective X (ω : Filter ℕ) x
    show matrixUltraproductRingHom X ω hω (star _) = star (matrixUltraproductRingHom X ω hω _)
    rw [TracialUltraproduct.tracialMatrixQuotient_star_mk, matrixUltraproductRingHom_mk,
      matrixUltraproductRingHom_mk, seqMap_star, star_mk]

theorem matrixUltraproductToHyperfiniteUltrapower_mk (hω : (ω : Filter ℕ) ≤ cofinite)
    (a : TracialUltraproduct.ModelBoundedSequence X) :
    matrixUltraproductToHyperfiniteUltrapower X ω hω
        (TracialUltraproduct.tracialMatrixQuotientMk X (ω : Filter ℕ) a) =
      mk hyperfiniteTracialVector ω (seqMap X a) :=
  matrixUltraproductRingHom_mk X ω hω a

/-- **`∏_ω M_k → 𝓡^ω` preserves the ultratraces.** -/
theorem ultratrace_matrixUltraproductToHyperfiniteUltrapower (hω : (ω : Filter ℕ) ≤ cofinite)
    (x : TracialUltraproduct.TracialMatrixQuotient X (ω : Filter ℕ)) :
    hyperfiniteUltratrace ω (matrixUltraproductToHyperfiniteUltrapower X ω hω x) =
      TracialUltraproduct.ultratraceCLM X ω x := by
  obtain ⟨a, rfl⟩ := TracialUltraproduct.tracialMatrixQuotientMk_surjective X (ω : Filter ℕ) x
  rw [TracialUltraproduct.ultratraceCLM_apply, TracialUltraproduct.ultratrace_mk,
    matrixUltraproductToHyperfiniteUltrapower_mk, TracialUltrapower.ultratrace_mk]
  apply UltrafilterLimit.ulim_eq
  have hf : Tendsto (fun n ↦ ((stageFactor X n : ℝ) : ℂ)) (ω : Filter ℕ) (nhds 1) := by
    have h := (Complex.continuous_ofReal.tendsto 1).comp
      ((tendsto_stageFactor X).mono_left (hω.trans Nat.cofinite_eq_atTop.le))
    rw [Complex.ofReal_one] at h
    exact h
  have hprod := hf.mul (TracialUltraproduct.tendsto_seqUltratrace X ω a)
  rw [one_mul] at hprod
  refine Filter.Tendsto.congr (fun n ↦ ?_) hprod
  show ((stageFactor X n : ℝ) : ℂ) * normTrace (X n) (a n) =
    ⟪deltaOne PauliGroup, stageCorner (stageEmbedding X n) (a n) (deltaOne PauliGroup)⟫_ℂ
  rw [GroupVonNeumann.inner_deltaOne_left PauliGroup, ← ambientCoefficientAtOne_apply,
    coefficient_stageCorner_eq_normTrace, stageFactor_complex]

end

#audit_axioms one_sub_stageFactor_le
#audit_axioms isNull_seqMap
#audit_axioms ultratrace_matrixUltraproductToHyperfiniteUltrapower

end Hyperfinite
end GroupApproximation
