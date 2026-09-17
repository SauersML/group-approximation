import GroupApproximation.Analysis.TracialUltrapowerTrace
import GroupApproximation.Analysis.FaithfulTracialState
import GroupApproximation.Meta.AxiomGuard

/-!
# Non-vacuity of the tracial ultrapower `M^ω`: nontriviality and the ultratrace state

Lane `sk-rows-08` (R^ω target non-vacuity).  `simple_kazhdan_sofic_group.tex`, subsection
"Brown's formulation":

> (tex 345–348) It is LEF, so it is sofic … and hyperlinear …, and $L(G)$ embeds in
> $\mathcal R^\omega$.

The corpus reads "embeds in `𝓡^ω`" as an injective unital `⋆`-homomorphism into
`TracialUltrapower.Ultrapower τ ω` carrying the canonical trace to the ultratrace.  This module
checks that the target is not degenerate, for every tracial ultrapower (every ultrafilter `ω`,
no freeness needed):

* `ultrapower_nontrivial`: `M^ω` is nontrivial, since `trω 1 = 1 ≠ 0 = trω 0`.
* `ultratrace_star_mul_self_real_nonneg`: `trω (x⋆x)` is a nonnegative real, as the `ω`-limit
  of the nonnegative reals `‖xₙ Ω‖²`.
* `ultratraceTracialState`: the ultratrace is a faithful tracial state (corpus
  `FaithfulTracialState`).
* `pullbackTracialState`, `nontrivial_of_starAlgHom`: an injective unital `⋆`-homomorphism
  `A → B` pulls a faithful tracial state of `B` back to one of `A`, and any unital
  `⋆`-homomorphism into a nontrivial algebra has a nontrivial (nonzero) domain.
-/

namespace GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity

open Filter
open scoped ComplexOrder

noncomputable section

universe u

section Ultrapower

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialUltrapower.TracialVector M) (ω : Ultrafilter ℕ)

/-- **`M^ω` is nontrivial**: the ultratrace takes the value `1` at `1` and `0` at `0`. -/
theorem ultrapower_nontrivial : Nontrivial (TracialUltrapower.Ultrapower τ ω) := by
  refine ⟨⟨1, 0, fun h ↦ ?_⟩⟩
  have h1 : TracialUltrapower.ultratrace τ ω 1 = TracialUltrapower.ultratrace τ ω 0 :=
    congrArg (fun x ↦ TracialUltrapower.ultratrace τ ω x) h
  rw [TracialUltrapower.ultratrace_one, map_zero] at h1
  exact one_ne_zero h1

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.ultrapower_nontrivial

/-- **Positivity of the ultratrace**: `trω (x⋆x)` is a nonnegative real number. -/
theorem ultratrace_star_mul_self_real_nonneg (x : TracialUltrapower.Ultrapower τ ω) :
    ∃ t : ℝ, 0 ≤ t ∧ TracialUltrapower.ultratrace τ ω (star x * x) = (t : ℂ) := by
  obtain ⟨a, rfl⟩ := TracialUltrapower.mk_surjective τ ω x
  rw [TracialUltrapower.star_mk, ← map_mul (TracialUltrapower.mk τ ω),
    TracialUltrapower.ultratrace_mk]
  have hT := TracialUltrapower.tendsto_seqUltratrace τ ω (star a * a)
  have hre : Tendsto (fun n ↦ (TracialUltrapower.seqTrace τ (star a * a) n).re) (ω : Filter ℕ)
      (nhds (TracialUltrapower.seqUltratrace τ ω (star a * a)).re) :=
    (Complex.continuous_re.tendsto _).comp hT
  have him : Tendsto (fun n ↦ (TracialUltrapower.seqTrace τ (star a * a) n).im) (ω : Filter ℕ)
      (nhds (TracialUltrapower.seqUltratrace τ ω (star a * a)).im) :=
    (Complex.continuous_im.tendsto _).comp hT
  have hre_nonneg : ∀ n, 0 ≤ (TracialUltrapower.seqTrace τ (star a * a) n).re := fun n ↦ by
    rw [TracialUltrapower.seqTrace_star_mul_self, Complex.ofReal_re]
    exact sq_nonneg _
  have him_zero : ∀ n, (TracialUltrapower.seqTrace τ (star a * a) n).im = 0 := fun n ↦ by
    rw [TracialUltrapower.seqTrace_star_mul_self, Complex.ofReal_im]
  have hconst : Tendsto (fun n ↦ (TracialUltrapower.seqTrace τ (star a * a) n).im)
      (ω : Filter ℕ) (nhds 0) :=
    Filter.Tendsto.congr (fun n ↦ (him_zero n).symm) tendsto_const_nhds
  have h0 : (TracialUltrapower.seqUltratrace τ ω (star a * a)).im = 0 :=
    tendsto_nhds_unique him hconst
  refine ⟨(TracialUltrapower.seqUltratrace τ ω (star a * a)).re, ge_of_tendsto' hre hre_nonneg, ?_⟩
  apply Complex.ext
  · rw [Complex.ofReal_re]
  · rw [Complex.ofReal_im, h0]

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.ultratrace_star_mul_self_real_nonneg

/-- The ultratrace as a complex-linear functional on `M^ω`. -/
def ultratraceLinear : TracialUltrapower.Ultrapower τ ω →ₗ[ℂ] ℂ where
  toFun := TracialUltrapower.ultratrace τ ω
  map_add' := map_add (TracialUltrapower.ultratrace τ ω)
  map_smul' c x := by
    change TracialUltrapower.ultratrace τ ω (c • x) = c * TracialUltrapower.ultratrace τ ω x
    exact TracialUltrapower.ultratrace_smul τ ω c x

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.ultratraceLinear

theorem ultratraceLinear_apply (x : TracialUltrapower.Ultrapower τ ω) :
    ultratraceLinear τ ω x = TracialUltrapower.ultratrace τ ω x :=
  rfl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.ultratraceLinear_apply

/-- **The ultratrace is a faithful tracial state on `M^ω`.** -/
def ultratraceTracialState : FaithfulTracialState (TracialUltrapower.Ultrapower τ ω) where
  toLinearMap := ultratraceLinear τ ω
  map_one := TracialUltrapower.ultratrace_one τ ω
  map_star_mul_self_nonneg x := by
    obtain ⟨t, ht, htr⟩ := ultratrace_star_mul_self_real_nonneg τ ω x
    have hle : (0 : ℂ) ≤ (t : ℂ) := Complex.zero_le_real.mpr ht
    rw [← htr] at hle
    exact hle
  map_mul_comm := TracialUltrapower.ultratrace_mul_comm τ ω
  eq_zero_of_map_star_mul_self_eq_zero := fun {x} hx ↦
    (TracialUltrapower.ultratrace_star_mul_self_eq_zero_iff τ ω x).mp hx

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.ultratraceTracialState

theorem ultratraceTracialState_apply (x : TracialUltrapower.Ultrapower τ ω) :
    ultratraceTracialState τ ω x = TracialUltrapower.ultratrace τ ω x :=
  rfl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.ultratraceTracialState_apply

end Ultrapower

section Pullback

variable {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [Ring B] [StarRing B] [Algebra ℂ B]

/-- **Pullback of a faithful tracial state** along an injective unital `⋆`-homomorphism. -/
def pullbackTracialState (t : FaithfulTracialState B) (Φ : A →⋆ₐ[ℂ] B)
    (hΦ : Function.Injective Φ) : FaithfulTracialState A where
  toLinearMap := t.toLinearMap.comp Φ.toAlgHom.toLinearMap
  map_one := by
    change t.toLinearMap (Φ 1) = 1
    rw [map_one]
    exact t.map_one
  map_star_mul_self_nonneg x := by
    have h := t.map_star_mul_self_nonneg (Φ x)
    rw [← map_star Φ x, ← map_mul Φ] at h
    exact h
  map_mul_comm x y := by
    have h := t.map_mul_comm (Φ x) (Φ y)
    rw [← map_mul Φ, ← map_mul Φ] at h
    exact h
  eq_zero_of_map_star_mul_self_eq_zero := fun {x} hx ↦ by
    have h : t.toLinearMap (star (Φ x) * Φ x) = 0 := by
      rw [← map_star Φ x, ← map_mul Φ]
      exact hx
    have h2 : Φ x = 0 := t.eq_zero_of_map_star_mul_self_eq_zero h
    exact hΦ (h2.trans (map_zero Φ).symm)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.pullbackTracialState

theorem pullbackTracialState_apply (t : FaithfulTracialState B) (Φ : A →⋆ₐ[ℂ] B)
    (hΦ : Function.Injective Φ) (a : A) : pullbackTracialState t Φ hΦ a = t (Φ a) :=
  rfl

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.pullbackTracialState_apply

/-- A unital `⋆`-homomorphism into a nontrivial algebra has a nontrivial domain. -/
theorem nontrivial_of_starAlgHom [Nontrivial B] (Φ : A →⋆ₐ[ℂ] B) : Nontrivial A := by
  refine ⟨⟨1, 0, fun h ↦ ?_⟩⟩
  have h1 : Φ 1 = Φ 0 := congrArg (fun a ↦ Φ a) h
  rw [map_one, map_zero] at h1
  exact one_ne_zero h1

#audit_axioms GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity.nontrivial_of_starAlgHom

end Pullback

end

end GroupApproximation.SimpleKazhdanSofic.SkRows.ROmegaSanity
