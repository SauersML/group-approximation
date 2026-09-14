import GroupApproximation.Analysis.TwistedGroupVonNeumannFactor
import GroupApproximation.Analysis.VonNeumannTwistedAmplification
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.LinearCombination
import GroupApproximation.Meta.AxiomGuard

/-!
# Products of twisted group von Neumann algebras: cocycles, ICC, and `ℓ²(Γ; ℓ²(A)) = ℓ²(Γ × A)`

Infrastructure of lane `oa-mcduff` for `simple_kazhdan_sofic_group.tex` at origin/main 37551fd93,
"Brown's formulation", tex 280–283 (census row `97438886a277`): "`L(G) ⊗̄ 𝓡` is a McDuff factor".
The tensor product `L_ρ(A) ⊗̄ L_σ(Γ)` of `Analysis/VonNeumannTwistedAmplification` is the twisted group
von Neumann algebra of `Γ × A` for the sum cocycle.  This module supplies the pieces that involve no
operators.

* `prodCocycle σ ρ`, `isSignCocycle_prodCocycle`: the sum cocycle `((γ,a),(δ,b)) ↦ σ(γ,δ) + ρ(a,b)`.
* `isTwistedICC_prodCocycle`: twisted ICC passes to products.
* `isTwistedICC_zero_of_isICC`: an ICC group is twisted ICC for the zero cocycle.
* `twistedLeftOperator_zero`, `groupVonNeumannAlgebra_eq_twisted_zero`: `L(G) = L_0(G)`.
* `curryLp`: the unitary `ℓ²(Γ; ℓ²(A)) ≃ ℓ²(Γ × A)`, `f ↦ ((γ, a) ↦ f γ a)`.
-/

namespace GroupApproximation
namespace TwistedProduct

open ReducedGroupCStarTrace TwistedGroupVonNeumann TwistedTensor
open scoped ENNReal InnerProductSpace

noncomputable section

universe u w

/-! ## The sum cocycle -/

section Cocycle

variable {Γ : Type u} {A : Type w} [Group Γ] [Group A]

/-- The sum cocycle on `Γ × A`. -/
def prodCocycle (σ : Γ → Γ → ZMod 2) (ρ : A → A → ZMod 2) (x y : Γ × A) : ZMod 2 :=
  σ x.1 y.1 + ρ x.2 y.2

theorem isSignCocycle_prodCocycle {σ : Γ → Γ → ZMod 2} {ρ : A → A → ZMod 2}
    (hσ : IsSignCocycle σ) (hρ : IsSignCocycle ρ) : IsSignCocycle (prodCocycle σ ρ) where
  map_one_left x := by
    simp only [prodCocycle, Prod.fst_one, Prod.snd_one, hσ.map_one_left, hρ.map_one_left, add_zero]
  map_one_right x := by
    simp only [prodCocycle, Prod.fst_one, Prod.snd_one, hσ.map_one_right, hρ.map_one_right,
      add_zero]
  cocycle x y z := by
    simp only [prodCocycle, Prod.fst_mul, Prod.snd_mul]
    linear_combination hσ.cocycle x.1 y.1 z.1 + hρ.cocycle x.2 y.2 z.2

/-- **Twisted ICC passes to products** of normalized cocycles. -/
theorem isTwistedICC_prodCocycle {σ : Γ → Γ → ZMod 2} {ρ : A → A → ZMod 2}
    (hσs : IsSignCocycle σ) (hρs : IsSignCocycle ρ) (hσ : IsTwistedICC σ) (hρ : IsTwistedICC ρ) :
    IsTwistedICC (prodCocycle σ ρ) := by
  intro x hx
  by_cases hx1 : x.1 = 1
  · have hx2 : x.2 ≠ 1 := fun h ↦ hx (Prod.ext hx1 h)
    rcases hρ x.2 hx2 with hinf | ⟨t, htc, hts⟩
    · left
      have hsub : (fun b : A ↦ ((x.1, b) : Γ × A)) '' {b : A | IsConj x.2 b} ⊆
          {y : Γ × A | IsConj x y} := by
        rintro _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc⟩ := isConj_iff.mp hb
        exact isConj_iff.mpr ⟨(1, c), Prod.ext (by simp) (by simpa using hc)⟩
      exact Set.Infinite.mono hsub
        ((Set.infinite_image_iff fun _ _ _ _ h ↦ (Prod.ext_iff.mp h).2).mpr hinf)
    · right
      refine ⟨(1, t), Prod.ext (by simp [hx1]) (by simpa using htc), ?_⟩
      intro h
      apply hts
      simp only [prodCocycle, hx1] at h
      exact add_left_cancel h
  · rcases hσ x.1 hx1 with hinf | ⟨t, htc, hts⟩
    · left
      have hsub : (fun b : Γ ↦ ((b, x.2) : Γ × A)) '' {b : Γ | IsConj x.1 b} ⊆
          {y : Γ × A | IsConj x y} := by
        rintro _ ⟨b, hb, rfl⟩
        obtain ⟨c, hc⟩ := isConj_iff.mp hb
        exact isConj_iff.mpr ⟨(c, 1), Prod.ext (by simpa using hc) (by simp)⟩
      exact Set.Infinite.mono hsub
        ((Set.infinite_image_iff fun _ _ _ _ h ↦ (Prod.ext_iff.mp h).1).mpr hinf)
    · right
      refine ⟨(t, 1), Prod.ext (by simpa using htc) (by simp), ?_⟩
      intro h
      apply hts
      simp only [prodCocycle, hρs.map_one_left, hρs.map_one_right, add_zero] at h
      exact h

/-- An ICC group is twisted ICC for the zero cocycle. -/
theorem isTwistedICC_zero_of_isICC {G : Type u} [Group G] (hG : TwoSidedRegularCommutant.IsICC G) :
    IsTwistedICC (fun _ _ : G ↦ (0 : ZMod 2)) :=
  fun g hg ↦ Or.inl (hG g hg)

theorem isSignCocycle_zero (G : Type u) [Group G] : IsSignCocycle (fun _ _ : G ↦ (0 : ZMod 2)) where
  map_one_left _ := rfl
  map_one_right _ := rfl
  cocycle _ _ _ := rfl

end Cocycle

/-! ## `L(G) = L_0(G)` -/

section Zero

variable (G : Type u) [Group G]

theorem twistedLeftOperator_zero (g : G) :
    twistedLeftOperator (fun _ _ : G ↦ (0 : ZMod 2)) g = leftRegularOperator G g := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext h
  rw [twistedLeftOperator_apply, zsign_zero, one_mul, leftRegularOperator_apply]

/-- **The group von Neumann algebra is the twisted one for the zero cocycle.** -/
theorem groupVonNeumannAlgebra_eq_twisted_zero :
    GroupVonNeumann.groupVonNeumannAlgebra G =
      twistedVonNeumannAlgebra (fun _ _ : G ↦ (0 : ZMod 2)) := by
  have hc : Set.centralizer (twistedGenerators (fun _ _ : G ↦ (0 : ZMod 2))) =
      Set.centralizer (Set.range (leftRegularOperator G)) := by
    apply le_antisymm
    · intro T hT m hm
      obtain ⟨g, rfl⟩ := hm
      exact hT _ (Set.mem_union_left _ ⟨g, twistedLeftOperator_zero G g⟩)
    · intro T hT m hm
      rcases hm with ⟨g, rfl⟩ | ⟨g, rfl⟩
      · rw [twistedLeftOperator_zero]
        exact hT _ ⟨g, rfl⟩
      · rw [twistedLeftOperator_zero, GroupVonNeumann.star_leftRegularOperator]
        exact hT _ ⟨g⁻¹, rfl⟩
  apply VonNeumannAlgebra.ext
  intro T
  change T ∈ Set.centralizer (Set.centralizer (Set.range (leftRegularOperator G))) ↔
    T ∈ Set.centralizer (Set.centralizer (twistedGenerators (fun _ _ : G ↦ (0 : ZMod 2))))
  rw [hc]

end Zero

/-! ## `ℓ²(Γ; ℓ²(A)) = ℓ²(Γ × A)` -/

section Curry

variable {Γ : Type u} {A : Type w}

theorem summable_sq_curry (f : VecHilbert Γ (lp (fun _ : A ↦ ℂ) 2)) :
    Summable (fun p : Γ × A ↦ ‖f p.1 p.2‖ ^ 2) := by
  have hrow : ∀ γ, ∑' a, ‖f γ a‖ ^ 2 = ‖f γ‖ ^ 2 := by
    intro γ
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (f γ)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    exact h.symm
  have hsum := (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).1 (lp.memℓp f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hsum
  refine (summable_prod_of_nonneg (fun _ ↦ sq_nonneg _)).2 ⟨fun γ ↦ ?_, ?_⟩
  · have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).1 (lp.memℓp (f γ))
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  · simpa only [hrow] using hsum

/-- The curried function of `f ∈ ℓ²(Γ; ℓ²(A))`, in `ℓ²(Γ × A)`. -/
def curryVec (f : VecHilbert Γ (lp (fun _ : A ↦ ℂ) 2)) : lp (fun _ : Γ × A ↦ ℂ) 2 :=
  ⟨fun p ↦ f p.1 p.2, by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using summable_sq_curry f⟩

theorem summable_sq_row (F : lp (fun _ : Γ × A ↦ ℂ) 2) :
    Summable (fun p : Γ × A ↦ ‖F p‖ ^ 2) := by
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).1 (lp.memℓp F)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- The row `a ↦ F (γ, a)` of `F ∈ ℓ²(Γ × A)`. -/
def uncurryRow (F : lp (fun _ : Γ × A ↦ ℂ) 2) (γ : Γ) : lp (fun _ : A ↦ ℂ) 2 :=
  ⟨fun a ↦ F (γ, a), by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      ((summable_prod_of_nonneg (fun _ ↦ sq_nonneg _)).1 (summable_sq_row F)).1 γ⟩

theorem norm_uncurryRow_sq (F : lp (fun _ : Γ × A ↦ ℂ) 2) (γ : Γ) :
    ‖uncurryRow F γ‖ ^ 2 = ∑' a, ‖F (γ, a)‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (uncurryRow F γ)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- The uncurried vector of `F ∈ ℓ²(Γ × A)`, in `ℓ²(Γ; ℓ²(A))`. -/
def uncurryVec (F : lp (fun _ : Γ × A ↦ ℂ) 2) : VecHilbert Γ (lp (fun _ : A ↦ ℂ) 2) :=
  ⟨fun γ ↦ uncurryRow F γ, by
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_uncurryRow_sq]
    exact ((summable_prod_of_nonneg (fun _ ↦ sq_nonneg _)).1 (summable_sq_row F)).2⟩

/-- Currying, as a linear equivalence. -/
def curryLinear : VecHilbert Γ (lp (fun _ : A ↦ ℂ) 2) ≃ₗ[ℂ] lp (fun _ : Γ × A ↦ ℂ) 2 where
  toFun := curryVec
  invFun := uncurryVec
  map_add' f g := by
    apply lp.ext
    funext p
    change (⇑(f + g)) p.1 p.2 = f p.1 p.2 + g p.1 p.2
    rw [lp.coeFn_add, Pi.add_apply, lp.coeFn_add, Pi.add_apply]
  map_smul' c f := by
    apply lp.ext
    funext p
    change (⇑(c • f)) p.1 p.2 = c • f p.1 p.2
    rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply]
  left_inv f := by
    apply lp.ext
    funext γ
    apply lp.ext
    funext a
    rfl
  right_inv F := by
    apply lp.ext
    funext p
    rfl

/-- **Currying is unitary**: `ℓ²(Γ; ℓ²(A)) ≃ ℓ²(Γ × A)`. -/
def curryLp : VecHilbert Γ (lp (fun _ : A ↦ ℂ) 2) ≃ₗᵢ[ℂ] lp (fun _ : Γ × A ↦ ℂ) 2 :=
  curryLinear.isometryOfInner (by
    intro f g
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    have hs : Summable fun p : Γ × A ↦ ⟪f p.1 p.2, g p.1 p.2⟫_ℂ :=
      lp.summable_inner (curryLinear f) (curryLinear g)
    have h₁ : ∀ γ : Γ, Summable fun a : A ↦ ⟪f γ a, g γ a⟫_ℂ :=
      fun γ ↦ lp.summable_inner (f γ) (g γ)
    calc ∑' p : Γ × A, ⟪(curryLinear f) p, (curryLinear g) p⟫_ℂ
        = ∑' p : Γ × A, ⟪f p.1 p.2, g p.1 p.2⟫_ℂ := rfl
      _ = ∑' (γ : Γ) (a : A), ⟪f γ a, g γ a⟫_ℂ := hs.tsum_prod' h₁
      _ = ∑' γ : Γ, ⟪f γ, g γ⟫_ℂ :=
        tsum_congr fun γ ↦ (lp.inner_eq_tsum (f γ) (g γ)).symm)

@[simp]
theorem curryLp_apply (f : VecHilbert Γ (lp (fun _ : A ↦ ℂ) 2)) (γ : Γ) (a : A) :
    curryLp f (γ, a) = f γ a :=
  rfl

end Curry

end

end TwistedProduct
end GroupApproximation

#audit_axioms GroupApproximation.TwistedProduct.isTwistedICC_prodCocycle
#audit_axioms GroupApproximation.TwistedProduct.groupVonNeumannAlgebra_eq_twisted_zero
#audit_axioms GroupApproximation.TwistedProduct.curryLp
