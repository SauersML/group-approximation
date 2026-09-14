import GroupApproximation.Analysis.TracialStandardFormCommutation
import GroupApproximation.Sofic.UltrafilterLimit
import GroupApproximation.Meta.AxiomGuard

/-!
# The tracial ultrapower `M^ω`

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93): "`L(G)` embeds in `𝓡^ω`" and "a McDuff factor that embeds in
`𝓡^ω`".

For a von Neumann algebra `M` on `H` and a unit vector `Ω` whose vector state `⟪Ω, ·Ω⟫` is a trace on
`M` (`TracialVector M`), the tracial ultrapower `M^ω` is the algebra of uniformly bounded sequences in
`M` modulo the sequences with `lim_ω ‖aₙΩ‖ = 0`, the `‖·‖₂`-null sequences.

* `TracialVector.ofStandardForm`: a tracial standard form supplies a tracial vector.
* `TracialVector.norm_star_apply`, `TracialVector.norm_mul_apply_le`: on `M`,
  `‖T⋆Ω‖ = ‖TΩ‖` and `‖(TS)Ω‖ ≤ ‖S‖ ‖TΩ‖`, both by traciality alone.
* `boundedSeq M`: the uniformly bounded `M`-valued sequences, a star subalgebra of `ℕ → B(H)`.
* `nullIdeal τ ω`: the `‖·‖₂`-null sequences, a two-sided star ideal.  Right multiplication is where
  traciality enters, and no square roots in `M` are needed.
* `Ultrapower τ ω`: the quotient `M^ω`, with its ring, complex algebra, star ring and star module
  structure, and the quotient map `mk`.

The ultratrace and the diagonal embedding `M → M^ω` are `Analysis/TracialUltrapowerTrace.lean`.
-/

namespace GroupApproximation
namespace TracialUltrapower

open Filter
open scoped InnerProductSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A tracial vector** for `M`: a unit vector whose vector state is a trace on `M`. -/
structure TracialVector (M : VonNeumannAlgebra H) where
  /-- The vector. -/
  vec : H
  /-- It is a unit vector. -/
  norm_vec : ‖vec‖ = 1
  /-- Its vector state is a trace on `M`. -/
  tracial : ∀ T ∈ M, ∀ S ∈ M, ⟪vec, (T * S) vec⟫_ℂ = ⟪vec, (S * T) vec⟫_ℂ

/-- A tracial standard form supplies a tracial vector. -/
def TracialVector.ofStandardForm {M : VonNeumannAlgebra H} {Ω : H}
    (h : TracialStandardForm.IsTracialStandardForm M Ω) : TracialVector M :=
  ⟨Ω, h.norm_omega, h.tracial⟩

variable {M : VonNeumannAlgebra H}

namespace TracialVector

variable (τ : TracialVector M)

theorem inner_star_mul_self (T : H →L[ℂ] H) :
    ⟪τ.vec, (star T * T) τ.vec⟫_ℂ = ((‖T τ.vec‖ ^ 2 : ℝ) : ℂ) := by
  show ⟪τ.vec, star T (T τ.vec)⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

theorem norm_apply_eq_of_inner_eq {T S : H →L[ℂ] H}
    (h : ⟪τ.vec, (star T * T) τ.vec⟫_ℂ = ⟪τ.vec, (star S * S) τ.vec⟫_ℂ) :
    ‖T τ.vec‖ = ‖S τ.vec‖ := by
  rw [inner_star_mul_self, inner_star_mul_self] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (Complex.ofReal_injective h)

/-- `‖T⋆Ω‖ = ‖TΩ‖` on `M`. -/
theorem norm_star_apply {T : H →L[ℂ] H} (hT : T ∈ M) : ‖star T τ.vec‖ = ‖T τ.vec‖ := by
  apply τ.norm_apply_eq_of_inner_eq
  rw [star_star]
  exact τ.tracial T hT (star T) (star_mem hT)

/-- **`‖(TS)Ω‖ ≤ ‖S‖ ‖TΩ‖` on `M`**, by traciality: `‖(TS)Ω‖ = ‖S⋆T⋆Ω‖`. -/
theorem norm_mul_apply_le {T S : H →L[ℂ] H} (hT : T ∈ M) (hS : S ∈ M) :
    ‖(T * S) τ.vec‖ ≤ ‖S‖ * ‖T τ.vec‖ := by
  have hTS : T * S ∈ M := mul_mem hT hS
  have h1 : ‖(T * S) τ.vec‖ = ‖(star S * star T) τ.vec‖ := by
    apply τ.norm_apply_eq_of_inner_eq
    have e1 : star (star S * star T) = T * S := by rw [star_mul, star_star, star_star]
    rw [e1]
    have e2 : star S * star T = star (T * S) := (star_mul T S).symm
    rw [e2]
    exact τ.tracial _ (star_mem hTS) _ hTS
  rw [h1]
  calc ‖(star S * star T) τ.vec‖ = ‖star S (star T τ.vec)‖ := rfl
    _ ≤ ‖star S‖ * ‖star T τ.vec‖ := (star S).le_opNorm _
    _ = ‖S‖ * ‖T τ.vec‖ := by
      rw [τ.norm_star_apply hT]
      exact congrArg (· * ‖T τ.vec‖) (norm_star S)

end TracialVector

/-! ## Bounded sequences -/

variable (M) in
/-- **Uniformly bounded sequences in `M`**, as a star subalgebra of `ℕ → B(H)`. -/
def boundedSeq : StarSubalgebra ℂ (ℕ → (H →L[ℂ] H)) where
  carrier := {a | (∀ n, a n ∈ M) ∧ ∃ C : ℝ, ∀ n, ‖a n‖ ≤ C}
  mul_mem' := by
    intro a b ha hb
    obtain ⟨ha, Ca, hCa⟩ := ha
    obtain ⟨hb, Cb, hCb⟩ := hb
    refine ⟨fun n ↦ mul_mem (ha n) (hb n), Ca * Cb, fun n ↦ ?_⟩
    exact (norm_mul_le (a n) (b n)).trans
      (mul_le_mul (hCa n) (hCb n) (norm_nonneg _) ((norm_nonneg _).trans (hCa n)))
  one_mem' := ⟨fun _ ↦ one_mem M, 1, fun _ ↦ ContinuousLinearMap.norm_id_le⟩
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha, Ca, hCa⟩ := ha
    obtain ⟨hb, Cb, hCb⟩ := hb
    exact ⟨fun n ↦ add_mem (ha n) (hb n), Ca + Cb,
      fun n ↦ (norm_add_le (a n) (b n)).trans (add_le_add (hCa n) (hCb n))⟩
  zero_mem' := ⟨fun _ ↦ zero_mem M, 0, fun _ ↦ by simp⟩
  algebraMap_mem' c :=
    ⟨fun _ ↦ M.toStarSubalgebra.algebraMap_mem c, ‖algebraMap ℂ (H →L[ℂ] H) c‖, fun _ ↦ le_rfl⟩
  star_mem' := by
    intro a ha
    obtain ⟨ha, C, hC⟩ := ha
    exact ⟨fun n ↦ star_mem (ha n), C, fun n ↦ (le_of_eq (norm_star (a n))).trans (hC n)⟩

theorem mem_boundedSeq_iff {a : ℕ → (H →L[ℂ] H)} :
    a ∈ boundedSeq M ↔ (∀ n, a n ∈ M) ∧ ∃ C : ℝ, ∀ n, ‖a n‖ ≤ C :=
  Iff.rfl

theorem coord_mem (a : boundedSeq M) (n : ℕ) : (a : ℕ → (H →L[ℂ] H)) n ∈ M :=
  (mem_boundedSeq_iff.mp a.2).1 n

theorem exists_bound (a : boundedSeq M) : ∃ C : ℝ, ∀ n, ‖(a : ℕ → (H →L[ℂ] H)) n‖ ≤ C :=
  (mem_boundedSeq_iff.mp a.2).2

/-! ## The `‖·‖₂`-null ideal -/

variable (τ : TracialVector M) (ω : Ultrafilter ℕ)

/-- A bounded sequence is **`‖·‖₂`-null along `ω`** when `‖aₙΩ‖ → 0` along `ω`. -/
def IsNull (a : boundedSeq M) : Prop :=
  Tendsto (fun n ↦ ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖) (ω : Filter ℕ) (nhds 0)

theorem isNull_zero : IsNull τ ω 0 := by
  show Tendsto (fun n ↦ ‖((0 : boundedSeq M) : ℕ → (H →L[ℂ] H)) n τ.vec‖) (ω : Filter ℕ) (nhds 0)
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, zero_apply, norm_zero]
  exact tendsto_const_nhds

theorem isNull_add {a b : boundedSeq M} (ha : IsNull τ ω a) (hb : IsNull τ ω b) :
    IsNull τ ω (a + b) := by
  have hg : Tendsto (fun n ↦ ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ + ‖(b : ℕ → (H →L[ℂ] H)) n τ.vec‖)
      (ω : Filter ℕ) (nhds 0) := by
    simpa using Filter.Tendsto.add ha hb
  exact squeeze_zero (fun n ↦ norm_nonneg _)
    (fun n ↦ norm_add_le ((a : ℕ → (H →L[ℂ] H)) n τ.vec) ((b : ℕ → (H →L[ℂ] H)) n τ.vec)) hg

theorem isNull_mul_left (b : boundedSeq M) {a : boundedSeq M} (ha : IsNull τ ω a) :
    IsNull τ ω (b * a) := by
  obtain ⟨C, hC⟩ := exists_bound b
  have hg : Tendsto (fun n ↦ C * ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖) (ω : Filter ℕ) (nhds 0) := by
    simpa using Filter.Tendsto.const_mul C ha
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hg
  calc ‖((b * a : boundedSeq M) : ℕ → (H →L[ℂ] H)) n τ.vec‖
      = ‖(b : ℕ → (H →L[ℂ] H)) n ((a : ℕ → (H →L[ℂ] H)) n τ.vec)‖ := rfl
    _ ≤ ‖(b : ℕ → (H →L[ℂ] H)) n‖ * ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ := mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)

theorem isNull_mul_right {a : boundedSeq M} (ha : IsNull τ ω a) (b : boundedSeq M) :
    IsNull τ ω (a * b) := by
  obtain ⟨C, hC⟩ := exists_bound b
  have hg : Tendsto (fun n ↦ C * ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖) (ω : Filter ℕ) (nhds 0) := by
    simpa using Filter.Tendsto.const_mul C ha
  refine squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hg
  calc ‖((a * b : boundedSeq M) : ℕ → (H →L[ℂ] H)) n τ.vec‖
      = ‖((a : ℕ → (H →L[ℂ] H)) n * (b : ℕ → (H →L[ℂ] H)) n) τ.vec‖ := rfl
    _ ≤ ‖(b : ℕ → (H →L[ℂ] H)) n‖ * ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ :=
      τ.norm_mul_apply_le (coord_mem a n) (coord_mem b n)
    _ ≤ C * ‖(a : ℕ → (H →L[ℂ] H)) n τ.vec‖ := mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)

theorem isNull_star {a : boundedSeq M} (ha : IsNull τ ω a) : IsNull τ ω (star a) :=
  Filter.Tendsto.congr (fun n ↦ (τ.norm_star_apply (coord_mem a n)).symm) ha

/-- **The `‖·‖₂`-null ideal** of bounded sequences along `ω`. -/
def nullIdeal : Ideal (boundedSeq M) where
  carrier := {a | IsNull τ ω a}
  zero_mem' := isNull_zero τ ω
  add_mem' := isNull_add τ ω
  smul_mem' := fun b _ ha ↦ isNull_mul_left τ ω b ha

instance nullIdeal_isTwoSided : (nullIdeal τ ω).IsTwoSided where
  mul_mem_of_left := fun b ha ↦ isNull_mul_right τ ω ha b

theorem mem_nullIdeal_iff (a : boundedSeq M) : a ∈ nullIdeal τ ω ↔ IsNull τ ω a :=
  Iff.rfl

theorem nullIdeal_star_mem {a : boundedSeq M} (ha : a ∈ nullIdeal τ ω) :
    star a ∈ nullIdeal τ ω :=
  isNull_star τ ω ha

/-! ## The quotient -/

/-- **The tracial ultrapower** `M^ω`. -/
def Ultrapower : Type u :=
  boundedSeq M ⧸ nullIdeal τ ω

noncomputable instance ultrapowerRing : Ring (Ultrapower τ ω) :=
  Ideal.Quotient.ring (nullIdeal τ ω)

noncomputable instance ultrapowerAlgebra : Algebra ℂ (Ultrapower τ ω) :=
  Ideal.Quotient.algebra ℂ

/-- The quotient map `ℓ^∞(M) → M^ω`. -/
def mk : boundedSeq M →+* Ultrapower τ ω :=
  Ideal.Quotient.mk (nullIdeal τ ω)

theorem mk_surjective : Function.Surjective (mk τ ω) :=
  Ideal.Quotient.mk_surjective

theorem mk_eq_zero_iff (a : boundedSeq M) : mk τ ω a = 0 ↔ IsNull τ ω a := by
  show Ideal.Quotient.mk (nullIdeal τ ω) a = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

theorem mk_smul (c : ℂ) (a : boundedSeq M) : mk τ ω (c • a) = c • mk τ ω a := by
  show Ideal.Quotient.mk (nullIdeal τ ω) (c • a) = c • Ideal.Quotient.mk (nullIdeal τ ω) a
  rw [← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]

private def starHom : boundedSeq M →+ Ultrapower τ ω :=
  (mk τ ω).toAddMonoidHom.comp starAddEquiv.toAddMonoidHom

private theorem nullIdeal_le_star_ker : (nullIdeal τ ω).toAddSubgroup ≤ (starHom τ ω).ker := by
  intro a ha
  change mk τ ω (star a) = 0
  rw [mk_eq_zero_iff]
  exact nullIdeal_star_mem τ ω ha

noncomputable instance ultrapowerStar : Star (Ultrapower τ ω) where
  star := QuotientAddGroup.lift (nullIdeal τ ω).toAddSubgroup (starHom τ ω)
    (nullIdeal_le_star_ker τ ω)

@[simp]
theorem star_mk (a : boundedSeq M) : star (mk τ ω a) = mk τ ω (star a) :=
  QuotientAddGroup.lift_mk _ _ _

noncomputable instance ultrapowerStarRing : StarRing (Ultrapower τ ω) where
  star_involutive x := by
    obtain ⟨a, rfl⟩ := mk_surjective τ ω x
    rw [star_mk, star_mk, star_star]
  star_mul x y := by
    obtain ⟨a, rfl⟩ := mk_surjective τ ω x
    obtain ⟨b, rfl⟩ := mk_surjective τ ω y
    rw [← map_mul (mk τ ω), star_mk, star_mk, star_mk, star_mul, map_mul]
  star_add x y := by
    obtain ⟨a, rfl⟩ := mk_surjective τ ω x
    obtain ⟨b, rfl⟩ := mk_surjective τ ω y
    rw [← map_add (mk τ ω), star_mk, star_mk, star_mk, star_add, map_add]

noncomputable instance ultrapowerStarModule : StarModule ℂ (Ultrapower τ ω) where
  star_smul c x := by
    obtain ⟨a, rfl⟩ := mk_surjective τ ω x
    rw [← mk_smul, star_mk, star_mk, star_smul, mk_smul]

end

#audit_axioms TracialVector.norm_mul_apply_le
#audit_axioms nullIdeal_star_mem

end TracialUltrapower
end GroupApproximation
