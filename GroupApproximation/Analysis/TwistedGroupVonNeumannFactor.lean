import GroupApproximation.Analysis.TwistedGroupVonNeumann
import GroupApproximation.Analysis.GroupVonNeumannIIOneFactor

/-!
# Twisted group von Neumann algebras that are II₁ factors

Infrastructure of lane `oa-hyperfinite` for "Brown's formulation" of `simple_kazhdan_sofic_group.tex`
(tex l.273–290 at 37551fd93): the hyperfinite II₁ factor `𝓡` is the twisted group von Neumann
algebra of the Pauli group (`Analysis/PauliHyperfiniteFactor.lean`), and `L(G) ⊗̄ 𝓡` is the twisted
algebra of `G × Γ`.  Both are II₁ factors by the single criterion proved here.

* `IsTwistedICC σ`: every `a ≠ 1` either has an infinite conjugacy class, or commutes with some `t`
  with `σ(t,a) ≠ σ(a,t)`.
* `coefficient_conj`: an operator commuting with `λ_t` and `ρ_{t⁻¹}` has a coefficient vector
  `ξ = Tδ₁` satisfying `s(σ(t,t⁻¹a)) s(σ(t⁻¹at,t⁻¹)) ξ(t⁻¹at) = s(σ(t,t⁻¹)) ξ(a)`.
* `exists_smul_one_of_mem_centralizer`: over a twisted-ICC cocycle, **the commutant of the twisted
  left and right operators is the scalars**.  An infinite class kills a coefficient by
  square-summability, as in `Analysis/TwoSidedRegularCommutant.lean`.  A commuting `t` with
  `σ(t,a) ≠ σ(a,t)` kills it by a sign: the two cocycle identities at `(t,a,t⁻¹)` and `(a,t,t⁻¹)`
  turn the relation above into `ξ(a) = -ξ(a)`.
* `isFactor`, `twistedTrace_isFaithfulNormalTracialState`, `not_finite_twistedVonNeumannAlgebra`,
  and `isIIOneFactor_twistedVonNeumannAlgebra`: an infinite group with a twisted-ICC sign cocycle
  gives a II₁ factor, in oa-mcduff's `IIOneFactor.IsIIOneFactor`.
-/

namespace GroupApproximation
namespace TwistedGroupVonNeumann

open ReducedGroupCStarTrace Filter
open scoped ENNReal InnerProductSpace ComplexOrder

noncomputable section

universe u

/-! ## Two facts about `ZMod 2` -/

theorem zmod_two_conj_aux {p X q r s c : ZMod 2} (h1 : p + X = q + r) (h2 : s + X = c + 0) :
    r + q = c + (p + s) := by
  revert h1 h2
  revert p X q r s c
  decide

theorem zmod_two_add_eq_one_of_ne {p q : ZMod 2} (h : p ≠ q) : p + q = 1 := by
  revert h
  revert p q
  decide

variable {Γ : Type u} [Group Γ]

local instance : DecidableEq Γ := Classical.decEq Γ

variable (σ : Γ → Γ → ZMod 2)

/-- **Twisted infinite conjugacy classes.**  Every `a ≠ 1` has an infinite conjugacy class, or
commutes with some `t` whose two cocycle values against `a` differ. -/
def IsTwistedICC : Prop :=
  ∀ a : Γ, a ≠ 1 →
    {x : Γ | IsConj a x}.Infinite ∨ ∃ t : Γ, t * a = a * t ∧ σ t a ≠ σ a t

/-- A twisted left translate of the identity point mass is a point mass. -/
theorem twistedLeftOperator_deltaOne (hσ : IsSignCocycle σ) (g : Γ) :
    twistedLeftOperator σ g (deltaOne Γ) = lp.single 2 g 1 := by
  apply lp.ext
  funext x
  simp only [twistedLeftOperator_apply, deltaOne, lp.coeFn_single]
  by_cases hx : x = g
  · subst hx
    simp [hσ.map_one_right]
  · have hne : x⁻¹ * x ≠ x⁻¹ * g := fun h ↦ hx (mul_left_cancel h)
    have hne' : g⁻¹ * x ≠ 1 := by
      intro h
      apply hx
      calc x = g * (g⁻¹ * x) := by rw [mul_inv_cancel_left]
        _ = g := by rw [h, mul_one]
    rw [Pi.single_eq_of_ne hne', Pi.single_eq_of_ne hx, mul_zero]

/-- The conjugation operator `λ_t ρ_{t⁻¹}` multiplies `δ₁` by `s(σ(t,t⁻¹))`. -/
theorem conj_deltaOne (hσ : IsSignCocycle σ) (t : Γ) :
    twistedLeftOperator σ t (twistedRightOperator σ t⁻¹ (deltaOne Γ)) =
      zsign (σ t t⁻¹) • deltaOne Γ := by
  apply lp.ext
  funext h
  change zsign (σ t (t⁻¹ * h)) *
      (zsign (σ (t⁻¹ * h * t⁻¹⁻¹) t⁻¹) * deltaOne Γ (t⁻¹ * h * t⁻¹⁻¹)) =
    zsign (σ t t⁻¹) * deltaOne Γ h
  rw [inv_inv]
  by_cases hh : h = 1
  · subst hh
    rw [mul_one, inv_mul_cancel, hσ.map_one_left, zsign_zero, one_mul,
      TwoSidedRegularCommutant.deltaOne_apply_self]
  · have harg : t⁻¹ * h * t ≠ 1 := by
      intro h'
      apply hh
      calc h = t * (t⁻¹ * h * t) * t⁻¹ := by group
        _ = 1 := by rw [h', mul_one, mul_inv_cancel]
    rw [TwoSidedRegularCommutant.deltaOne_apply_ne Γ harg,
      TwoSidedRegularCommutant.deltaOne_apply_ne Γ hh, mul_zero, mul_zero, mul_zero]

/-- **The coefficient relation.**  If `T` commutes with `λ_t` and `ρ_{t⁻¹}`, its coefficient vector
transforms by a sign under conjugation by `t`. -/
theorem coefficient_conj (hσ : IsSignCocycle σ) {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (t : Γ) (hl : twistedLeftOperator σ t * T = T * twistedLeftOperator σ t)
    (hr : twistedRightOperator σ t⁻¹ * T = T * twistedRightOperator σ t⁻¹) (h : Γ) :
    zsign (σ t (t⁻¹ * h)) * (zsign (σ (t⁻¹ * h * t) t⁻¹) * T (deltaOne Γ) (t⁻¹ * h * t)) =
      zsign (σ t t⁻¹) * T (deltaOne Γ) h := by
  have hcomm : twistedLeftOperator σ t (twistedRightOperator σ t⁻¹ (T (deltaOne Γ))) =
      zsign (σ t t⁻¹) • T (deltaOne Γ) := by
    have h1 : twistedRightOperator σ t⁻¹ (T (deltaOne Γ)) =
        T (twistedRightOperator σ t⁻¹ (deltaOne Γ)) :=
      DFunLike.congr_fun hr (deltaOne Γ)
    have h2 : twistedLeftOperator σ t (T (twistedRightOperator σ t⁻¹ (deltaOne Γ))) =
        T (twistedLeftOperator σ t (twistedRightOperator σ t⁻¹ (deltaOne Γ))) :=
      DFunLike.congr_fun hl _
    rw [h1, h2, conj_deltaOne σ hσ, map_smul]
  have hx := congrArg (fun F : GroupHilbert Γ ↦ F h) hcomm
  simp only [twistedLeftOperator_apply, twistedRightOperator_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, inv_inv] at hx
  exact hx

/-- The sign in the coefficient relation at a commuting element. -/
theorem sign_conj_of_commute (hσ : IsSignCocycle σ) {t a : Γ} (hta : t * a = a * t) :
    σ t (t⁻¹ * a) + σ (t⁻¹ * a * t) t⁻¹ = σ t t⁻¹ + (σ t a + σ a t) := by
  have hc1 : t⁻¹ * a = a * t⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hta, inv_mul_cancel_left]
  have hc2 : t⁻¹ * a * t = a := by rw [mul_assoc, hta, inv_mul_cancel_left]
  have h1 := hσ.cocycle t a t⁻¹
  have h2 := hσ.cocycle a t t⁻¹
  rw [mul_inv_cancel, hσ.map_one_right] at h2
  rw [hta] at h1
  rw [hc1, hc2]
  exact zmod_two_conj_aux h1 h2

/-- A coefficient at a commuting element with differing cocycle values vanishes. -/
theorem coefficient_eq_zero_of_commute (hσ : IsSignCocycle σ)
    {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ} {t a : Γ}
    (hl : twistedLeftOperator σ t * T = T * twistedLeftOperator σ t)
    (hr : twistedRightOperator σ t⁻¹ * T = T * twistedRightOperator σ t⁻¹)
    (hta : t * a = a * t) (hne : σ t a ≠ σ a t) : T (deltaOne Γ) a = 0 := by
  have hrel := coefficient_conj σ hσ t hl hr a
  have hc2 : t⁻¹ * a * t = a := by rw [mul_assoc, hta, inv_mul_cancel_left]
  rw [hc2, zsign_mul_zsign_mul, hc2.symm ▸ sign_conj_of_commute σ hσ hta,
    zmod_two_add_eq_one_of_ne hne, zsign_add, zsign_one] at hrel
  have hs := zsign_mul_self (σ t t⁻¹)
  set s := zsign (σ t t⁻¹)
  set x := T (deltaOne Γ) a
  linear_combination (-s / 2) * hrel - x * hs

/-- A coefficient on an infinite conjugacy class vanishes. -/
theorem coefficient_eq_zero_of_infinite (hσ : IsSignCocycle σ)
    {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (hl : ∀ t : Γ, twistedLeftOperator σ t * T = T * twistedLeftOperator σ t)
    (hr : ∀ t : Γ, twistedRightOperator σ t * T = T * twistedRightOperator σ t)
    {a : Γ} (hinf : {x : Γ | IsConj a x}.Infinite) : T (deltaOne Γ) a = 0 := by
  set f := T (deltaOne Γ) with hf_def
  have hnorm : ∀ t h : Γ, ‖f (t⁻¹ * h * t)‖ = ‖f h‖ := by
    intro t h
    have hrel := congrArg norm (coefficient_conj σ hσ t (hl t) (hr t⁻¹) h)
    simpa only [norm_mul, norm_zsign, one_mul] using hrel
  by_contra hfa
  have hsubset : {y : Γ | IsConj a y} ⊆
      {y : Γ | ¬ ‖f y‖ ^ (2 : ℝ≥0∞).toReal < ‖f a‖ ^ (2 : ℝ≥0∞).toReal} := by
    rintro y hy
    obtain ⟨c, hc⟩ := isConj_iff.mp hy
    have harg : c⁻¹ * y * c = a := by
      rw [← hc, mul_assoc c a c⁻¹, inv_mul_cancel_left, inv_mul_cancel_right]
    have hfy : ‖f a‖ = ‖f y‖ := by
      rw [← hnorm c y, harg]
    rw [Set.mem_setOf_eq, ← hfy]
    exact lt_irrefl _
  have hsum : Summable fun y : Γ ↦ ‖f y‖ ^ (2 : ℝ≥0∞).toReal :=
    (memℓp_gen_iff (by norm_num)).1 (lp.memℓp f)
  have hev : ∀ᶠ y in cofinite,
      ‖f y‖ ^ (2 : ℝ≥0∞).toReal < ‖f a‖ ^ (2 : ℝ≥0∞).toReal :=
    hsum.tendsto_cofinite_zero.eventually_lt_const
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hfa) _)
  have hfin : {y : Γ | ¬ ‖f y‖ ^ (2 : ℝ≥0∞).toReal
      < ‖f a‖ ^ (2 : ℝ≥0∞).toReal}.Finite :=
    eventually_cofinite.mp hev
  exact (hinf.mono hsubset) hfin

/-- **The commutant of the twisted two-sided regular representation is the scalars**, over a
twisted-ICC sign cocycle. -/
theorem exists_smul_one_of_mem_centralizer (hσ : IsSignCocycle σ) (hG : IsTwistedICC σ)
    {T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ}
    (hT : T ∈ Set.centralizer
      (Set.range (twistedLeftOperator σ) ∪ Set.range (twistedRightOperator σ))) :
    ∃ c : ℂ, T = c • 1 := by
  have hl : ∀ g : Γ, twistedLeftOperator σ g * T = T * twistedLeftOperator σ g :=
    fun g ↦ hT _ (Set.mem_union_left _ ⟨g, rfl⟩)
  have hr : ∀ g : Γ, twistedRightOperator σ g * T = T * twistedRightOperator σ g :=
    fun g ↦ hT _ (Set.mem_union_right _ ⟨g, rfl⟩)
  set c : ℂ := T (deltaOne Γ) 1 with hc_def
  have hf : T (deltaOne Γ) = c • deltaOne Γ := by
    apply lp.ext
    funext x
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    by_cases hx : x = 1
    · subst hx
      rw [TwoSidedRegularCommutant.deltaOne_apply_self, mul_one]
    · rw [TwoSidedRegularCommutant.deltaOne_apply_ne Γ hx, mul_zero]
      rcases hG x hx with hinf | ⟨t, hta, hne⟩
      · exact coefficient_eq_zero_of_infinite σ hσ hl hr hinf
      · exact coefficient_eq_zero_of_commute σ hσ (hl t) (hr t⁻¹) hta hne
  refine ⟨c, ?_⟩
  have hdelta : ∀ g : Γ,
      T (lp.single 2 g 1) = c • (lp.single 2 g 1 : GroupHilbert Γ) := by
    intro g
    rw [← twistedRightOperator_deltaOne σ hσ]
    calc T (twistedRightOperator σ g (deltaOne Γ))
        = twistedRightOperator σ g (T (deltaOne Γ)) :=
          (DFunLike.congr_fun (hr g) (deltaOne Γ)).symm
      _ = twistedRightOperator σ g (c • deltaOne Γ) := by rw [hf]
      _ = c • twistedRightOperator σ g (deltaOne Γ) := map_smul _ _ _
  apply ContinuousLinearMap.ext
  intro F
  have hbase : HasSum (fun g : Γ ↦ (lp.single 2 g (F g) : GroupHilbert Γ)) F :=
    lp.hasSum_single (by norm_num) F
  have hcoordsum : ∀ g : Γ,
      T (lp.single 2 g (F g)) = c • (lp.single 2 g (F g) : GroupHilbert Γ) := by
    intro g
    have h1 : (lp.single 2 g (F g) : GroupHilbert Γ)
        = F g • (lp.single 2 g 1 : GroupHilbert Γ) := by
      calc (lp.single 2 g (F g) : GroupHilbert Γ)
          = lp.single 2 g (F g • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
        _ = F g • (lp.single 2 g 1 : GroupHilbert Γ) :=
          lp.single_smul 2 g (F g) 1
    rw [h1, map_smul, hdelta g, smul_comm]
  have hTsum : HasSum (fun g : Γ ↦ T (lp.single 2 g (F g))) (T F) :=
    hbase.mapL T
  have hcsum : HasSum (fun g : Γ ↦ T (lp.single 2 g (F g))) (c • F) := by
    have hsmul := hbase.const_smul c
    have hfun : (fun g : Γ ↦ T (lp.single 2 g (F g)))
        = fun g : Γ ↦ c • (lp.single 2 g (F g) : GroupHilbert Γ) :=
      funext hcoordsum
    rw [hfun]
    exact hsmul
  calc T F = c • F := hTsum.unique hcsum
    _ = (c • (1 : GroupHilbert Γ →L[ℂ] GroupHilbert Γ)) F := rfl

/-! ## The II₁ factor -/

/-- **`L_σ(Γ)` is a factor** over a twisted-ICC sign cocycle. -/
theorem isFactor (hσ : IsSignCocycle σ) (hG : IsTwistedICC σ) :
    TracialStandardForm.IsFactor (twistedVonNeumannAlgebra σ) := by
  intro T hTm hTc
  apply exists_smul_one_of_mem_centralizer σ hσ hG
  rintro m (⟨g, rfl⟩ | ⟨g, rfl⟩)
  · exact VonNeumannAlgebra.mem_commutant_iff.mp hTc _ (twistedLeftOperator_mem σ g)
  · exact commutes_twistedRightOperator σ hσ hTm g

/-- The identity coefficient is a normal functional on `L_σ(Γ)`. -/
theorem twistedTrace_isNormalFunctional :
    IIOneFactor.IsNormalFunctional (twistedVonNeumannAlgebra σ) (IIOneFactor.groupTrace Γ) := by
  refine ⟨fun n ↦ if n = 0 then deltaOne Γ else 0,
    fun n ↦ if n = 0 then deltaOne Γ else 0, ?_, ?_⟩
  · apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa using hn
    simp [hn0]
  · intro T _hT
    rw [tsum_eq_single 0]
    · simp [IIOneFactor.groupTrace]
    · intro n hn
      simp [hn]

/-- **The identity coefficient is a faithful normal tracial state on `L_σ(Γ)`.** -/
theorem twistedTrace_isFaithfulNormalTracialState (hσ : IsSignCocycle σ) :
    IIOneFactor.IsFaithfulNormalTracialState (twistedVonNeumannAlgebra σ)
      (IIOneFactor.groupTrace Γ) where
  normal := twistedTrace_isNormalFunctional σ
  map_one := by
    rw [IIOneFactor.groupTrace_eq_coefficient]
    exact GroupVonNeumann.coefficient_one Γ
  nonneg := fun T _ ↦ IIOneFactor.groupTrace_star_mul_self_nonneg Γ T
  tracial := fun T hT S hS ↦ by
    rw [IIOneFactor.groupTrace_eq_coefficient, IIOneFactor.groupTrace_eq_coefficient]
    exact coefficient_mul_comm σ hσ hT hS
  faithful := fun T hT h ↦ by
    rw [IIOneFactor.groupTrace_eq_coefficient] at h
    exact eq_zero_of_mem_of_coefficient_star_mul_self_eq_zero σ hσ hT h

/-- The twisted left operators are linearly independent in `L_σ(Γ)`. -/
theorem linearIndependent_twistedLeftOperator (hσ : IsSignCocycle σ) :
    LinearIndependent ℂ
      (fun g : Γ ↦ (⟨twistedLeftOperator σ g, twistedLeftOperator_mem σ g⟩ :
        ↥(twistedVonNeumannAlgebra σ).toStarSubalgebra)) := by
  let ev : ↥(twistedVonNeumannAlgebra σ).toStarSubalgebra →ₗ[ℂ] GroupHilbert Γ :=
    { toFun := fun T ↦ (T : GroupHilbert Γ →L[ℂ] GroupHilbert Γ) (deltaOne Γ)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  apply LinearIndependent.of_comp ev
  have hcomp : ev ∘ (fun g : Γ ↦ (⟨twistedLeftOperator σ g, twistedLeftOperator_mem σ g⟩ :
        ↥(twistedVonNeumannAlgebra σ).toStarSubalgebra)) =
      fun g : Γ ↦ (lp.single 2 g (1 : ℂ) : GroupHilbert Γ) := by
    funext g
    exact twistedLeftOperator_deltaOne σ hσ g
  rw [hcomp]
  exact (IIOneFactor.orthonormal_groupHilbert_single Γ).linearIndependent

/-- Over an infinite group, `L_σ(Γ)` is infinite-dimensional. -/
theorem not_finite_twistedVonNeumannAlgebra [Infinite Γ] (hσ : IsSignCocycle σ) :
    ¬ Module.Finite ℂ ↥(twistedVonNeumannAlgebra σ).toStarSubalgebra := by
  intro hfin
  exact Module.Finite.not_linearIndependent_of_infinite _
    (linearIndependent_twistedLeftOperator σ hσ)

/-- **Over an infinite group with a twisted-ICC sign cocycle, `L_σ(Γ)` is a II₁ factor.** -/
theorem isIIOneFactor_twistedVonNeumannAlgebra [Infinite Γ] (hσ : IsSignCocycle σ)
    (hG : IsTwistedICC σ) :
    IIOneFactor.IsIIOneFactor (twistedVonNeumannAlgebra σ) where
  isFactor := isFactor σ hσ hG
  infinite_dimensional := not_finite_twistedVonNeumannAlgebra σ hσ
  exists_trace := ⟨IIOneFactor.groupTrace Γ, twistedTrace_isFaithfulNormalTracialState σ hσ⟩

end

#audit_axioms exists_smul_one_of_mem_centralizer
#audit_axioms isFactor
#audit_axioms twistedTrace_isFaithfulNormalTracialState
#audit_axioms isIIOneFactor_twistedVonNeumannAlgebra

end TwistedGroupVonNeumann
end GroupApproximation
