import GroupApproximation.Analysis.TracialUltrapower

/-!
# The ultratrace on `M^ω`, and the diagonal embedding `M → M^ω`

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93).  `Analysis/TracialUltrapower.lean` builds `M^ω` for a von Neumann
algebra `M` with a tracial vector `Ω`; this module equips it with its trace.

* `seqUltratrace τ ω a = lim_ω ⟪Ω, aₙ Ω⟫`, which exists because `‖⟪Ω, aₙ Ω⟫‖ ≤ ‖aₙ‖`.  It vanishes
  on `‖·‖₂`-null sequences, since `‖⟪Ω, aₙ Ω⟫‖ ≤ ‖aₙ Ω‖`, so it descends to `ultratrace τ ω` on `M^ω`.
* The ultratrace is additive, complex homogeneous, normalized, tracial, `⋆`-compatible and positive,
  and faithful: `ultratrace (x⋆x) = 0 ↔ x = 0`.
* `mkStarAlgHom`: the quotient map as a `⋆`-algebra homomorphism.
* `diag τ ω : M →⋆ₐ[ℂ] M^ω`, the constant sequences.  It preserves the trace
  (`ultratrace_diag`), and it is injective when `Ω` separates `M` (`diag_injective`), in particular
  for a tracial standard form.
-/

namespace GroupApproximation
namespace TracialUltrapower

open Filter
open scoped InnerProductSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialVector M) (ω : Ultrafilter ℕ)

/-! ## Vector-state bounds -/

theorem TracialVector.norm_inner_apply_le_norm_apply (T : H →L[ℂ] H) :
    ‖⟪τ.vec, T τ.vec⟫_ℂ‖ ≤ ‖T τ.vec‖ := by
  calc ‖⟪τ.vec, T τ.vec⟫_ℂ‖ ≤ ‖τ.vec‖ * ‖T τ.vec‖ := norm_inner_le_norm _ _
    _ = ‖T τ.vec‖ := by rw [τ.norm_vec, one_mul]

theorem TracialVector.norm_apply_le (T : H →L[ℂ] H) : ‖T τ.vec‖ ≤ ‖T‖ := by
  calc ‖T τ.vec‖ ≤ ‖T‖ * ‖τ.vec‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [τ.norm_vec, mul_one]

theorem TracialVector.norm_inner_apply_le (T : H →L[ℂ] H) : ‖⟪τ.vec, T τ.vec⟫_ℂ‖ ≤ ‖T‖ :=
  (τ.norm_inner_apply_le_norm_apply T).trans (τ.norm_apply_le T)

/-! ## The trace along a sequence -/

/-- The coordinate traces `⟪Ω, aₙ Ω⟫` of a bounded sequence. -/
def seqTrace (a : boundedSeq M) (n : ℕ) : ℂ :=
  ⟪τ.vec, (a : ℕ → (H →L[ℂ] H)) n τ.vec⟫_ℂ

theorem exists_tendsto_seqTrace (a : boundedSeq M) :
    ∃ L : ℂ, Tendsto (seqTrace τ a) (ω : Filter ℕ) (nhds L) := by
  obtain ⟨C, hC⟩ := exists_bound a
  exact UltrafilterLimit.exists_tendsto_of_bounded ω (C := C)
    fun n ↦ (τ.norm_inner_apply_le _).trans (hC n)

/-- **`lim_ω ⟪Ω, aₙ Ω⟫`**, the ultratrace of a bounded sequence. -/
def seqUltratrace (a : boundedSeq M) : ℂ :=
  UltrafilterLimit.ulim ω (seqTrace τ a)

theorem tendsto_seqUltratrace (a : boundedSeq M) :
    Tendsto (seqTrace τ a) (ω : Filter ℕ) (nhds (seqUltratrace τ ω a)) :=
  UltrafilterLimit.tendsto_ulim (exists_tendsto_seqTrace τ ω a)

theorem seqUltratrace_eq_zero_of_isNull {a : boundedSeq M} (ha : IsNull τ ω a) :
    seqUltratrace τ ω a = 0 := by
  apply UltrafilterLimit.ulim_eq
  exact squeeze_zero_norm (fun n ↦ τ.norm_inner_apply_le_norm_apply _) ha

theorem seqUltratrace_add (a b : boundedSeq M) :
    seqUltratrace τ ω (a + b) = seqUltratrace τ ω a + seqUltratrace τ ω b := by
  apply UltrafilterLimit.ulim_eq
  refine Filter.Tendsto.congr (fun n ↦ ?_)
    ((tendsto_seqUltratrace τ ω a).add (tendsto_seqUltratrace τ ω b))
  show ⟪τ.vec, (a : ℕ → (H →L[ℂ] H)) n τ.vec⟫_ℂ + ⟪τ.vec, (b : ℕ → (H →L[ℂ] H)) n τ.vec⟫_ℂ =
    ⟪τ.vec, ((a : ℕ → (H →L[ℂ] H)) n + (b : ℕ → (H →L[ℂ] H)) n) τ.vec⟫_ℂ
  rw [add_apply, inner_add_right]

theorem seqUltratrace_smul (c : ℂ) (a : boundedSeq M) :
    seqUltratrace τ ω (c • a) = c * seqUltratrace τ ω a := by
  apply UltrafilterLimit.ulim_eq
  refine Filter.Tendsto.congr (fun n ↦ ?_) ((tendsto_seqUltratrace τ ω a).const_mul c)
  show c * ⟪τ.vec, (a : ℕ → (H →L[ℂ] H)) n τ.vec⟫_ℂ =
    ⟪τ.vec, (c • (a : ℕ → (H →L[ℂ] H)) n) τ.vec⟫_ℂ
  rw [smul_apply, inner_smul_right]

theorem seqUltratrace_one : seqUltratrace τ ω 1 = 1 := by
  apply UltrafilterLimit.ulim_eq
  refine Filter.Tendsto.congr (fun n ↦ ?_) (tendsto_const_nhds (x := (1 : ℂ)))
  show (1 : ℂ) = ⟪τ.vec, (1 : H →L[ℂ] H) τ.vec⟫_ℂ
  rw [one_apply_eq_self, inner_self_eq_norm_sq_to_K, τ.norm_vec]
  simp

theorem seqUltratrace_mul_comm (a b : boundedSeq M) :
    seqUltratrace τ ω (a * b) = seqUltratrace τ ω (b * a) := by
  unfold seqUltratrace
  congr 1
  funext n
  exact τ.tracial _ (coord_mem a n) _ (coord_mem b n)

theorem seqUltratrace_star (a : boundedSeq M) :
    seqUltratrace τ ω (star a) = starRingEnd ℂ (seqUltratrace τ ω a) := by
  unfold seqUltratrace
  rw [← UltrafilterLimit.ulim_conj (exists_tendsto_seqTrace τ ω a)]
  congr 1
  funext n
  show ⟪τ.vec, star ((a : ℕ → (H →L[ℂ] H)) n) τ.vec⟫_ℂ =
    starRingEnd ℂ ⟪τ.vec, (a : ℕ → (H →L[ℂ] H)) n τ.vec⟫_ℂ
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_conj_symm]

theorem seqTrace_star_mul_self (a : boundedSeq M) (n : ℕ) :
    seqTrace τ (star a * a) n = ((‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ ^ 2 : ℝ) : ℂ) :=
  τ.inner_star_mul_self _

theorem seqUltratrace_star_mul_self_eq_zero_iff (a : boundedSeq M) :
    seqUltratrace τ ω (star a * a) = 0 ↔ IsNull τ ω a := by
  have hnonneg : ∀ n, 0 ≤ ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ ^ 2 := fun n ↦ sq_nonneg _
  constructor
  · intro h0
    have h := tendsto_seqUltratrace τ ω (star a * a)
    rw [h0] at h
    have hn := h.norm
    rw [norm_zero] at hn
    have hsq : Tendsto (fun n ↦ ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ ^ 2) (ω : Filter ℕ) (nhds 0) := by
      refine Filter.Tendsto.congr (fun n ↦ ?_) hn
      rw [seqTrace_star_mul_self, Complex.norm_of_nonneg (hnonneg n)]
    have hsqrt := hsq.sqrt
    rw [Real.sqrt_zero] at hsqrt
    exact Filter.Tendsto.congr (fun n ↦ Real.sqrt_sq (norm_nonneg _)) hsqrt
  · intro ha
    apply UltrafilterLimit.ulim_eq
    have hsq : Tendsto (fun n ↦ ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ ^ 2) (ω : Filter ℕ) (nhds 0) := by
      simpa [sq] using ha.mul ha
    have hc : Tendsto (fun n ↦ ((‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ ^ 2 : ℝ) : ℂ)) (ω : Filter ℕ)
        (nhds 0) := by
      have h := (Complex.continuous_ofReal.tendsto 0).comp hsq
      rw [Complex.ofReal_zero] at h
      exact h
    exact Filter.Tendsto.congr (fun n ↦ (seqTrace_star_mul_self τ a n).symm) hc

/-- The coordinate trace as an additive map on bounded sequences. -/
def seqUltratraceHom : boundedSeq M →+ ℂ where
  toFun := seqUltratrace τ ω
  map_zero' := seqUltratrace_eq_zero_of_isNull τ ω (isNull_zero τ ω)
  map_add' := seqUltratrace_add τ ω

theorem nullIdeal_le_ultratrace_ker :
    (nullIdeal τ ω).toAddSubgroup ≤ (seqUltratraceHom τ ω).ker := by
  intro a ha
  exact seqUltratrace_eq_zero_of_isNull τ ω ha

/-! ## The ultratrace on `M^ω` -/

/-- **The ultratrace** on `M^ω`: the class of `a` goes to `lim_ω ⟪Ω, aₙ Ω⟫`. -/
def ultratrace : Ultrapower τ ω →+ ℂ :=
  QuotientAddGroup.lift (nullIdeal τ ω).toAddSubgroup (seqUltratraceHom τ ω)
    (nullIdeal_le_ultratrace_ker τ ω)

@[simp]
theorem ultratrace_mk (a : boundedSeq M) : ultratrace τ ω (mk τ ω a) = seqUltratrace τ ω a :=
  QuotientAddGroup.lift_mk _ _ _

theorem ultratrace_smul (c : ℂ) (x : Ultrapower τ ω) :
    ultratrace τ ω (c • x) = c * ultratrace τ ω x := by
  obtain ⟨a, rfl⟩ := mk_surjective τ ω x
  rw [← mk_smul, ultratrace_mk, ultratrace_mk, seqUltratrace_smul]

theorem ultratrace_one : ultratrace τ ω 1 = 1 := by
  rw [← map_one (mk τ ω), ultratrace_mk, seqUltratrace_one]

/-- **Traciality.** -/
theorem ultratrace_mul_comm (x y : Ultrapower τ ω) :
    ultratrace τ ω (x * y) = ultratrace τ ω (y * x) := by
  obtain ⟨a, rfl⟩ := mk_surjective τ ω x
  obtain ⟨b, rfl⟩ := mk_surjective τ ω y
  rw [← map_mul (mk τ ω), ← map_mul (mk τ ω), ultratrace_mk, ultratrace_mk,
    seqUltratrace_mul_comm]

theorem ultratrace_star (x : Ultrapower τ ω) :
    ultratrace τ ω (star x) = starRingEnd ℂ (ultratrace τ ω x) := by
  obtain ⟨a, rfl⟩ := mk_surjective τ ω x
  rw [star_mk, ultratrace_mk, ultratrace_mk, seqUltratrace_star]

/-- **Faithfulness**: `trω (x⋆x) = 0` forces `x = 0`. -/
theorem ultratrace_star_mul_self_eq_zero_iff (x : Ultrapower τ ω) :
    ultratrace τ ω (star x * x) = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := mk_surjective τ ω x
  rw [star_mk, ← map_mul (mk τ ω), ultratrace_mk, seqUltratrace_star_mul_self_eq_zero_iff,
    mk_eq_zero_iff]

/-! ## Homomorphisms -/

/-- The quotient map `ℓ^∞(M) → M^ω` as a `⋆`-algebra homomorphism. -/
def mkStarAlgHom : boundedSeq M →⋆ₐ[ℂ] Ultrapower τ ω where
  toAlgHom := Ideal.Quotient.mkₐ ℂ (nullIdeal τ ω)
  map_star' a := (star_mk τ ω a).symm

theorem mkStarAlgHom_apply (a : boundedSeq M) : mkStarAlgHom τ ω a = mk τ ω a :=
  rfl

variable (M) in
/-- The constant sequences. -/
def constSeq : ↥M.toStarSubalgebra →⋆ₐ[ℂ] boundedSeq M where
  toFun T := ⟨fun _ ↦ (T : H →L[ℂ] H), fun _ ↦ T.2, ‖(T : H →L[ℂ] H)‖, fun _ ↦ le_rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/-- **The diagonal embedding** `M → M^ω`. -/
def diag : ↥M.toStarSubalgebra →⋆ₐ[ℂ] Ultrapower τ ω :=
  (mkStarAlgHom τ ω).comp (constSeq M)

theorem diag_apply (T : ↥M.toStarSubalgebra) : diag τ ω T = mk τ ω (constSeq M T) :=
  rfl

/-- **The diagonal embedding preserves the trace.** -/
theorem ultratrace_diag (T : ↥M.toStarSubalgebra) :
    ultratrace τ ω (diag τ ω T) = ⟪τ.vec, (T : H →L[ℂ] H) τ.vec⟫_ℂ := by
  rw [diag_apply, ultratrace_mk]
  show UltrafilterLimit.ulim ω (fun _ : ℕ ↦ ⟪τ.vec, (T : H →L[ℂ] H) τ.vec⟫_ℂ) = _
  exact UltrafilterLimit.ulim_const ω ⟪τ.vec, (T : H →L[ℂ] H) τ.vec⟫_ℂ

/-- **The diagonal embedding is injective** when `Ω` separates `M`. -/
theorem diag_injective (hsep : ∀ T ∈ M, T τ.vec = 0 → T = 0) :
    Function.Injective (diag τ ω) := by
  refine (injective_iff_map_eq_zero (diag τ ω)).mpr fun T hT ↦ ?_
  rw [diag_apply, mk_eq_zero_iff] at hT
  have hconst : ‖(T : H →L[ℂ] H) τ.vec‖ = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds (x := ‖(T : H →L[ℂ] H) τ.vec‖)) hT
  apply Subtype.ext
  exact hsep _ T.2 (norm_eq_zero.mp hconst)

/-- A tracial standard form embeds diagonally in its ultrapower. -/
theorem diag_injective_of_standardForm {Ω : H}
    (h : TracialStandardForm.IsTracialStandardForm M Ω) :
    Function.Injective (diag (TracialVector.ofStandardForm h) ω) :=
  diag_injective _ ω h.separating

end

#audit_axioms ultratrace_mul_comm
#audit_axioms ultratrace_star_mul_self_eq_zero_iff
#audit_axioms ultratrace_diag
#audit_axioms diag_injective

end TracialUltrapower
end GroupApproximation
