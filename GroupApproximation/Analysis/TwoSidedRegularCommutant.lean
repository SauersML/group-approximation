import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful

/-!
# The two-sided regular representation has scalar commutant over an ICC group

Proof-ledger row `LI.06d`.  Its sentence, `p:limits-trace`, is:

> for faithfully traced unital C\*-coordinates `A` the left and right actions
> on `L²(A,τ)` generate a von Neumann algebra that need not be finite: for an
> infinite-dimensional II₁ factor in standard form it is all of `B(L²(A,τ))`.

The row records that nothing in the tree spoke about standard form.  This
module is the keystone of the route that will: the **commutant computation**.
For a group `G` with infinite conjugacy classes, every bounded operator on
`ℓ²(G)` commuting with both regular representations is a scalar.  The standard
form of the group von Neumann algebra `L(G)` is `ℓ²(G)` itself, its left and
right actions extend the two regular representations, so once the commutant of
`λ(G) ∪ ρ(G)` is scalar, the algebra the two actions generate — the double
centralizer — is all of `B(ℓ²(G))`.  No Tomita–Takesaki theory enters: the
computation is the classical coefficient argument, run at the level of `ℓ²`
summability.

Both regular representations already exist in the tree —
`ReducedGroupCStarTrace.leftRegularOperator` and, in the faithfulness module,
`ReducedGroupCStarTrace.rightRegularOperator` with the convention
`(ρ(g)f)(x) = f(xg⁻¹)` — and are reused, not redefined.

* `conj_fixes_deltaOne` — the conjugation operator `λ_t ∘ ρ_{t⁻¹}` fixes the
  identity point mass.
* `IsICC` — every nonidentity conjugacy class is infinite.
* `conjugationInvariant_eq_smul_deltaOne` — the coefficient argument: an `ℓ²`
  function invariant under conjugation is supported at the identity, because
  a nonzero value elsewhere would be attained on an infinite conjugacy class,
  against square-summability.
* `exists_smul_one_of_mem_centralizer` — the commutant: an operator commuting
  with `λ(G) ∪ ρ(G)` has a conjugation-invariant coefficient vector `T δ₁`,
  so `T δ₁ = c·δ₁`, so `T` is `c` on every point mass, so `T = c·1` by
  continuity through the point-mass expansion.

The von Neumann packaging, the trace, and the II₁ properties of `L(G)` are the
following modules' work; nothing here mentions them.
-/

namespace GroupApproximation
namespace TwoSidedRegularCommutant

open ReducedGroupCStarTrace Filter
open scoped ENNReal InnerProductSpace

noncomputable section

universe u

variable (G : Type u) [Group G]

local instance : DecidableEq G := Classical.decEq G

/-! ## The identity point mass, coordinatewise -/

@[simp]
theorem deltaOne_apply_self : deltaOne G 1 = 1 := by
  simp [deltaOne]

theorem deltaOne_apply_ne {x : G} (hx : x ≠ 1) : deltaOne G x = 0 := by
  simp [deltaOne, lp.single_apply, Pi.single_eq_of_ne hx]

/-- The conjugation operator `λ_t ∘ ρ_{t⁻¹}` fixes the identity point mass. -/
theorem conj_fixes_deltaOne (t : G) :
    leftRegularOperator G t (rightRegularOperator G t⁻¹ (deltaOne G))
      = deltaOne G := by
  apply lp.ext
  funext x
  change deltaOne G (t⁻¹ * x * (t⁻¹)⁻¹) = deltaOne G x
  rw [inv_inv]
  by_cases hx : x = 1
  · subst hx
    rw [mul_one, inv_mul_cancel]
  · have harg : t⁻¹ * x * t ≠ 1 := by
      intro h
      apply hx
      have h2 : x = t * (t⁻¹ * x * t) * t⁻¹ := by
        rw [mul_assoc t⁻¹ x t, mul_inv_cancel_left, mul_inv_cancel_right]
      rw [h2, h, mul_one, mul_inv_cancel]
    rw [deltaOne_apply_ne G harg, deltaOne_apply_ne G hx]

/-! ## Infinite conjugacy classes and the coefficient argument -/

/-- **Infinite conjugacy classes.**  Every element other than the identity has
an infinite conjugacy class. -/
def IsICC : Prop :=
  ∀ g : G, g ≠ 1 → {x : G | IsConj g x}.Infinite

variable {G}

/-- **The coefficient argument.**  An `ℓ²` function invariant under
conjugation is supported at the identity: over an ICC group a nonzero value at
`x ≠ 1` would be attained on the whole infinite conjugacy class of `x`,
against square-summability.  So the function is a multiple of `δ₁`. -/
theorem conjugationInvariant_eq_smul_deltaOne (hG : IsICC G)
    {f : GroupHilbert G} (hf : ∀ t x : G, f (t⁻¹ * x * t) = f x) :
    f = f 1 • deltaOne G := by
  have hcoord : ∀ x : G, f x = f 1 * deltaOne G x := by
    intro x
    by_cases hx : x = 1
    · subst hx
      rw [deltaOne_apply_self, mul_one]
    · have hzero : f x = 0 := by
        by_contra hfx
        -- the conjugacy class of `x` carries the value `f x`
        have hsubset : {y : G | IsConj x y} ⊆
            {y : G | ¬ ‖f y‖ ^ (2 : ℝ≥0∞).toReal
              < ‖f x‖ ^ (2 : ℝ≥0∞).toReal} := by
          rintro y hy
          obtain ⟨c, hc⟩ := isConj_iff.mp hy
          have harg : c⁻¹ * y * c = x := by
            rw [← hc, mul_assoc c x c⁻¹, inv_mul_cancel_left,
              inv_mul_cancel_right]
          have hfy : f x = f y := by
            have h := hf c y
            rw [harg] at h
            exact h
          rw [Set.mem_setOf_eq, ← hfy]
          exact lt_irrefl _
        -- square-summability makes that set finite
        have hsum : Summable fun y : G ↦ ‖f y‖ ^ (2 : ℝ≥0∞).toReal :=
          (memℓp_gen_iff (by norm_num)).1 (lp.memℓp f)
        have hev : ∀ᶠ y in cofinite,
            ‖f y‖ ^ (2 : ℝ≥0∞).toReal < ‖f x‖ ^ (2 : ℝ≥0∞).toReal :=
          hsum.tendsto_cofinite_zero.eventually_lt_const
            (Real.rpow_pos_of_pos (norm_pos_iff.mpr hfx) _)
        have hfin : {y : G | ¬ ‖f y‖ ^ (2 : ℝ≥0∞).toReal
            < ‖f x‖ ^ (2 : ℝ≥0∞).toReal}.Finite :=
          eventually_cofinite.mp hev
        exact ((hG x hx).mono hsubset) hfin
      rw [hzero, deltaOne_apply_ne G hx, mul_zero]
  apply lp.ext
  funext x
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  exact hcoord x

/-! ## The commutant of the two-sided regular representation -/

variable (G)

/-- **The commutant is scalar.**  Over an ICC group, a bounded operator on
`ℓ²(G)` commuting with the left and right regular representations is a scalar
multiple of the identity.  This is the analytic content of "the two actions in
standard form generate all of `B(L²)`": the generated von Neumann algebra is
the double centralizer, and the centralizer just computed is `ℂ·1`. -/
theorem exists_smul_one_of_mem_centralizer (hG : IsICC G)
    {T : GroupHilbert G →L[ℂ] GroupHilbert G}
    (hT : T ∈ Set.centralizer
      (Set.range (leftRegularOperator G)
        ∪ Set.range (rightRegularOperator G))) :
    ∃ c : ℂ, T = c • 1 := by
  -- the two commutation families, one operator at a time
  have hleft : ∀ g : G,
      leftRegularOperator G g * T = T * leftRegularOperator G g :=
    fun g ↦ hT _ (Set.mem_union_left _ ⟨g, rfl⟩)
  have hright : ∀ g : G,
      rightRegularOperator G g * T = T * rightRegularOperator G g :=
    fun g ↦ hT _ (Set.mem_union_right _ ⟨g, rfl⟩)
  -- the coefficient vector is conjugation-invariant
  have hinv : ∀ t x : G, T (deltaOne G) (t⁻¹ * x * t) = T (deltaOne G) x := by
    intro t x
    have hcomm : leftRegularOperator G t
        (rightRegularOperator G t⁻¹ (T (deltaOne G))) = T (deltaOne G) := by
      have h1 : rightRegularOperator G t⁻¹ (T (deltaOne G))
          = T (rightRegularOperator G t⁻¹ (deltaOne G)) :=
        DFunLike.congr_fun (hright t⁻¹) (deltaOne G)
      have h2 : leftRegularOperator G t
          (T (rightRegularOperator G t⁻¹ (deltaOne G)))
          = T (leftRegularOperator G t
              (rightRegularOperator G t⁻¹ (deltaOne G))) :=
        DFunLike.congr_fun (hleft t) _
      rw [h1, h2, conj_fixes_deltaOne]
    have hx : leftRegularOperator G t
        (rightRegularOperator G t⁻¹ (T (deltaOne G))) x
          = T (deltaOne G) x := by
      rw [hcomm]
    have hx' : T (deltaOne G) (t⁻¹ * x * (t⁻¹)⁻¹) = T (deltaOne G) x := hx
    rwa [inv_inv] at hx'
  have hf : T (deltaOne G) = T (deltaOne G) 1 • deltaOne G :=
    conjugationInvariant_eq_smul_deltaOne hG hinv
  refine ⟨T (deltaOne G) 1, ?_⟩
  set c : ℂ := T (deltaOne G) 1 with hc_def
  -- `T` is `c` on every point mass, which is a right translate of `δ₁`
  have hdelta : ∀ g : G,
      T (lp.single 2 g 1) = c • (lp.single 2 g 1 : GroupHilbert G) := by
    intro g
    rw [← rightRegular_deltaOne]
    calc T (rightRegularOperator G g (deltaOne G))
        = rightRegularOperator G g (T (deltaOne G)) :=
          (DFunLike.congr_fun (hright g) (deltaOne G)).symm
      _ = rightRegularOperator G g (c • deltaOne G) := by rw [hf]
      _ = c • rightRegularOperator G g (deltaOne G) := map_smul _ _ _
  -- hence `T = c • 1`, by continuity through the point-mass expansion
  apply ContinuousLinearMap.ext
  intro F
  have hbase : HasSum (fun g : G ↦ (lp.single 2 g (F g) : GroupHilbert G)) F :=
    lp.hasSum_single (by norm_num) F
  have hcoordsum : ∀ g : G,
      T (lp.single 2 g (F g)) = c • (lp.single 2 g (F g) : GroupHilbert G) := by
    intro g
    have h1 : (lp.single 2 g (F g) : GroupHilbert G)
        = F g • (lp.single 2 g 1 : GroupHilbert G) := by
      calc (lp.single 2 g (F g) : GroupHilbert G)
          = lp.single 2 g (F g • (1 : ℂ)) := by rw [smul_eq_mul, mul_one]
        _ = F g • (lp.single 2 g 1 : GroupHilbert G) :=
          lp.single_smul 2 g (F g) 1
    rw [h1, map_smul, hdelta g, smul_comm]
  have hTsum : HasSum (fun g : G ↦ T (lp.single 2 g (F g))) (T F) :=
    hbase.mapL T
  have hcsum : HasSum (fun g : G ↦ T (lp.single 2 g (F g))) (c • F) := by
    have hsmul := hbase.const_smul c
    have hfun : (fun g : G ↦ T (lp.single 2 g (F g)))
        = fun g : G ↦ c • (lp.single 2 g (F g) : GroupHilbert G) :=
      funext hcoordsum
    rw [hfun]
    exact hsmul
  calc T F = c • F := hTsum.unique hcsum
    _ = (c • (1 : GroupHilbert G →L[ℂ] GroupHilbert G)) F := rfl

end

end TwoSidedRegularCommutant
end GroupApproximation
