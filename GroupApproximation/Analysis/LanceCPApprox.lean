import GroupApproximation.Analysis.LanceHypertrace
import GroupApproximation.Analysis.LanceMultiplicativeDomain
import GroupApproximation.Analysis.LanceDayEngine

/-!
# From a completely positive approximation to an invariant mean

Toward proof-ledger row `RE.05` (the Lance debt).  This is the assembly of
the Lance lane: a group whose bounded operators admit unital completely
positive approximations of the identity, with values in `L(G)` and almost
fixing the left translations, is amenable.

The argument is the manuscript's.  Fix a finite `F ⊆ G` and a tolerance;
take a completely positive `φ` with `‖φ(λ_s) − λ_s‖` small on `F ∪ F⁻¹`.
The functional

  `f ↦ Re τ(φ(m_f))`   (`Analysis/LanceMultiplicationOperator`)

is finitely additive, positive and normalized because `φ` and the trace are.
It is *almost* invariant because translating the symbol is conjugating by a
left translation (`leftRegular_conj_mulOp`), conjugation commutes with `φ` up
to the multiplicative-domain estimate
(`Analysis/LanceMultiplicativeDomain.norm_map_conj_sub_conj_map_le`), and the
trace does not see conjugation at all
(`Analysis/LanceHypertrace.coefficientAtOne_conj_leftRegular`).  Day's
ultrafilter limit (`Analysis/LanceDayEngine`) turns the family into an
honest invariant mean.

The tolerance bookkeeping is the only arithmetic: the estimate costs
`2√(2δ)`, so a target `ε` is met by asking for `δ = ε²/8`.

## Manuscript status

Infrastructure for the Lance lane; certifies no manuscript step on its own.
`RE.05` remains conditional until the full compression statement lands.
-/

namespace GroupApproximation
namespace CStarExactness

open scoped InnerProductSpace
open ReducedGroupCStarTrace GroupVonNeumann Amenability

noncomputable section

universe u v w

/-- A completely positive map is positive: the `n = 1` amplification. -/
theorem map_nonneg_of_completelyPositive {A : Type u} {B : Type v}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    {φ : A →ₗ[ℂ] B} (hφ : IsCompletelyPositive φ) {a : A} (ha : 0 ≤ a) :
    0 ≤ φ a := by
  classical
  obtain ⟨b, hb⟩ := exists_star_mul_self_of_nonneg ha
  set N : CStarMatrix (Fin 1) (Fin 1) A :=
    ((fun _ _ ↦ b : Matrix (Fin 1) (Fin 1) A) :
      CStarMatrix (Fin 1) (Fin 1) A) with hN_def
  have hN00 : N 0 0 = b := by rw [hN_def]
  have hstarN : (star N : CStarMatrix (Fin 1) (Fin 1) A) 0 0
      = star (N 0 0) := Matrix.star_apply _ _ _
  have hM00 : (star N * N) 0 0 = a := by
    calc (star N * N) 0 0
        = ∑ t : Fin 1, (star N) 0 t * N t 0 := Matrix.mul_apply
      _ = (star N) 0 0 * N 0 0 := Fin.sum_univ_one _
      _ = star (N 0 0) * N 0 0 := by rw [hstarN]
      _ = star b * b := by rw [hN00]
      _ = a := hb.symm
  obtain ⟨P, hP⟩ := hφ 1 (star N * N) ⟨N, rfl⟩
  have hstarP : (star P : CStarMatrix (Fin 1) (Fin 1) B) 0 0
      = star (P 0 0) := Matrix.star_apply _ _ _
  have hPentry : (star P * P) 0 0 = star (P 0 0) * P 0 0 := by
    calc (star P * P) 0 0
        = ∑ t : Fin 1, (star P) 0 t * P t 0 := Matrix.mul_apply
      _ = (star P) 0 0 * P 0 0 := Fin.sum_univ_one _
      _ = star (P 0 0) * P 0 0 := by rw [hstarP]
  have hval : φ a = star (P 0 0) * P 0 0 := by
    calc φ a = φ ((star N * N) 0 0) := by rw [hM00]
      _ = ((star N * N).map ⇑φ) 0 0 := rfl
      _ = (star P * P) 0 0 :=
          congrArg (fun T : CStarMatrix (Fin 1) (Fin 1) B ↦ T 0 0) hP
      _ = star (P 0 0) * P 0 0 := hPentry
  rw [hval]
  exact star_mul_self_nonneg _

variable {G : Type} [Group G]

/-! ## The multiplication operator of a bounded real symbol -/

/-- The diagonal operator of a bounded real symbol. -/
def bddSymbol (f : G → ℝ) (hf : IsBddFun f) :
    GroupHilbert G →L[ℂ] GroupHilbert G :=
  mulOp (fun g ↦ ((f g : ℝ) : ℂ)) hf.choose (fun g ↦ by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hf.choose_spec g)

@[simp]
theorem bddSymbol_apply (f : G → ℝ) (hf : IsBddFun f)
    (x : GroupHilbert G) (g : G) :
    bddSymbol f hf x g = ((f g : ℝ) : ℂ) * x g := rfl

theorem bddSymbol_add (f₁ f₂ : G → ℝ) (hf₁ : IsBddFun f₁)
    (hf₂ : IsBddFun f₂) (hf : IsBddFun (f₁ + f₂)) :
    bddSymbol (f₁ + f₂) hf = bddSymbol f₁ hf₁ + bddSymbol f₂ hf₂ := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  show (((f₁ g + f₂ g : ℝ)) : ℂ) * x g
      = ((f₁ g : ℝ) : ℂ) * x g + ((f₂ g : ℝ) : ℂ) * x g
  push_cast
  ring

theorem bddSymbol_const (c : ℝ) (hf : IsBddFun (fun _ : G ↦ c)) :
    bddSymbol (fun _ : G ↦ c) hf
      = ((c : ℝ) : ℂ) • (1 : GroupHilbert G →L[ℂ] GroupHilbert G) := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  show ((c : ℝ) : ℂ) * x g = (((c : ℝ) : ℂ) • x) g
  rw [lp.coeFn_smul, Pi.smul_apply]
  rfl

theorem bddSymbol_nonneg (f : G → ℝ) (hf : IsBddFun f)
    (hpos : ∀ x, 0 ≤ f x) :
    (0 : GroupHilbert G →L[ℂ] GroupHilbert G) ≤ bddSymbol f hf :=
  mulOp_nonneg f hf.choose hpos _

theorem norm_bddSymbol_le (f : G → ℝ) (hf : IsBddFun f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : ‖bddSymbol f hf‖ ≤ C := by
  have hCbound : ∀ g : G, ‖((f g : ℝ) : ℂ)‖ ≤ C := by
    intro g
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hC g
  rw [bddSymbol, mulOp_congr _ _ C _ hCbound]
  exact norm_mulOp_le _ C hCbound

/-- Translating the symbol is conjugating by a left translation. -/
theorem bddSymbol_conj (s : G) (f : G → ℝ) (hf : IsBddFun f)
    (hfs : IsBddFun (fun x ↦ f (s * x))) :
    bddSymbol (fun x ↦ f (s * x)) hfs
      = leftRegularOperator G s⁻¹ * bddSymbol f hf
          * star (leftRegularOperator G s⁻¹) := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  have hstar : star (leftRegularOperator G s⁻¹)
      = leftRegularOperator G s := by
    rw [star_leftRegularOperator, inv_inv]
  rw [hstar]
  show ((f (s * g) : ℝ) : ℂ) * x g
      = ((f (s⁻¹⁻¹ * g) : ℝ) : ℂ) * x (s⁻¹ * (s⁻¹⁻¹ * g))
  rw [inv_inv, inv_mul_cancel_left]

/-! ## Unitarity of the left translations -/

theorem star_leftRegularOperator_mul (s : G) :
    star (leftRegularOperator G s) * leftRegularOperator G s = 1 := by
  rw [star_leftRegularOperator]
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  show (leftRegularOperator G s⁻¹ (leftRegularOperator G s x)) g = x g
  show (leftRegularOperator G s x) (s⁻¹⁻¹ * g) = x g
  show x (s⁻¹ * (s⁻¹⁻¹ * g)) = x g
  rw [inv_inv, inv_mul_cancel_left]

theorem leftRegularOperator_mul_star (s : G) :
    leftRegularOperator G s * star (leftRegularOperator G s) = 1 := by
  rw [star_leftRegularOperator]
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  show (leftRegularOperator G s (leftRegularOperator G s⁻¹ x)) g = x g
  show (leftRegularOperator G s⁻¹ x) (s⁻¹ * g) = x g
  show x (s⁻¹⁻¹ * (s⁻¹ * g)) = x g
  rw [inv_inv, mul_inv_cancel_left]

/-! ## The assembly -/

/-- `ℓ²(G)` is nontrivial: `δ₁` is a unit vector. -/
theorem nontrivial_groupHilbert : Nontrivial (GroupHilbert G) := by
  refine ⟨⟨deltaOne G, 0, fun h ↦ ?_⟩⟩
  have h1 : ‖deltaOne G‖ = 1 := norm_deltaOne G
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

/-- **The Lance assembly.**  A group whose bounded operators carry unital
completely positive approximations of the identity, with values in `L(G)`
and almost fixing every left translation, has an invariant mean. -/
theorem hasInvariantMean_of_cpApprox
    (h : ∀ (F : Finset G) (ε : ℝ), 0 < ε →
      ∃ φ : (GroupHilbert G →L[ℂ] GroupHilbert G) →ₗ[ℂ]
            (GroupHilbert G →L[ℂ] GroupHilbert G),
        IsCompletelyPositive φ ∧ φ 1 = 1 ∧
        (∀ T, φ T ∈ groupVonNeumannAlgebra G) ∧
        (∀ g ∈ F, ‖φ (leftRegularOperator G g)
          - leftRegularOperator G g‖ ≤ ε)) :
    HasInvariantMean G := by
  classical
  haveI : Nontrivial (GroupHilbert G) := nontrivial_groupHilbert
  haveI : Nontrivial (GroupHilbert G →L[ℂ] GroupHilbert G) := by
    obtain ⟨a, b, hab⟩ := (nontrivial_groupHilbert (G := G)).exists_pair_ne
    exact ⟨⟨1, 0, fun hcon ↦ hab (by
      have h1 : a = 0 := by
        have : (1 : GroupHilbert G →L[ℂ] GroupHilbert G) a = 0 := by
          rw [hcon]; rfl
        exact this
      have h2 : b = 0 := by
        have : (1 : GroupHilbert G →L[ℂ] GroupHilbert G) b = 0 := by
          rw [hcon]; rfl
        exact this
      rw [h1, h2])⟩⟩
  refine hasInvariantMean_of_approxMeans G fun F ε hε ↦ ?_
  obtain ⟨φ, hcp, hone, hrange, hclose⟩ :=
    h (F ∪ F.image (fun g ↦ g⁻¹)) (ε ^ 2 / 8) (by positivity)
  refine ⟨⟨fun f ↦ if hf : IsBddFun f
      then (coefficientAtOne (φ (bddSymbol f hf))).re else 0,
    ?_, ?_, ?_, ?_⟩⟩
  · -- additivity
    intro f₁ f₂ hf₁ hf₂
    rw [dif_pos (hf₁.add hf₂), dif_pos hf₁, dif_pos hf₂,
      bddSymbol_add f₁ f₂ hf₁ hf₂, map_add]
    show (coefficientAtOne (φ (bddSymbol f₁ hf₁)
        + φ (bddSymbol f₂ hf₂))).re = _
    rw [coefficientAtOne_add, Complex.add_re]
  · -- positivity
    intro f hf hpos
    rw [dif_pos hf]
    obtain ⟨r, hr0, hr⟩ := coefficientAtOne_nonneg
      (map_nonneg_of_completelyPositive hcp (bddSymbol_nonneg f hf hpos))
    rw [hr, Complex.ofReal_re]
    exact hr0
  · -- normalization
    intro c
    rw [dif_pos (IsBddFun.const c), bddSymbol_const c, map_smul, hone,
      coefficientAtOne_smul, coefficientAtOne_one, mul_one,
      Complex.ofReal_re]
  · -- almost invariance
    intro g hg f C hC
    have hf : IsBddFun f := ⟨C, hC⟩
    have hgf : IsBddFun (fun x ↦ f (g * x)) := ⟨C, fun x ↦ hC (g * x)⟩
    have hC0 : 0 ≤ C := le_trans (abs_nonneg (f 1)) (hC 1)
    rw [dif_pos hgf, dif_pos hf]
    -- the translated symbol is a conjugate
    have hsym : bddSymbol (fun x ↦ f (g * x)) hgf
        = leftRegularOperator G g⁻¹ * bddSymbol f hf
            * star (leftRegularOperator G g⁻¹) :=
      bddSymbol_conj g f hf hgf
    -- the trace does not see the conjugation
    have htrace : coefficientAtOne (leftRegularOperator G g⁻¹
          * φ (bddSymbol f hf) * star (leftRegularOperator G g⁻¹))
        = coefficientAtOne (φ (bddSymbol f hf)) :=
      coefficientAtOne_conj_leftRegular g⁻¹ (hrange _)
    -- the multiplicative-domain estimate
    have hginv : g⁻¹ ∈ F ∪ F.image (fun g ↦ g⁻¹) :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hg)
    have hδ := hclose g⁻¹ hginv
    have hest := norm_map_conj_sub_conj_map_le φ hcp hone
      (u := leftRegularOperator G g⁻¹)
      (star_leftRegularOperator_mul g⁻¹)
      (leftRegularOperator_mul_star g⁻¹)
      (U := leftRegularOperator G g⁻¹)
      (by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact star_leftRegularOperator_mul g⁻¹)
      (by
        rw [← ContinuousLinearMap.star_eq_adjoint]
        exact leftRegularOperator_mul_star g⁻¹)
      hδ (bddSymbol f hf)
    -- assemble
    have hdiff : (coefficientAtOne (φ (bddSymbol (fun x ↦ f (g * x)) hgf))).re
        - (coefficientAtOne (φ (bddSymbol f hf))).re
        = (coefficientAtOne (φ (bddSymbol (fun x ↦ f (g * x)) hgf)
            - leftRegularOperator G g⁻¹ * φ (bddSymbol f hf)
              * star (leftRegularOperator G g⁻¹))).re := by
      rw [show coefficientAtOne (φ (bddSymbol (fun x ↦ f (g * x)) hgf)
            - leftRegularOperator G g⁻¹ * φ (bddSymbol f hf)
              * star (leftRegularOperator G g⁻¹))
          = coefficientAtOne (φ (bddSymbol (fun x ↦ f (g * x)) hgf))
            - coefficientAtOne (leftRegularOperator G g⁻¹
                * φ (bddSymbol f hf)
                * star (leftRegularOperator G g⁻¹)) from rfl,
        htrace, Complex.sub_re]
    rw [hdiff]
    calc |(coefficientAtOne (φ (bddSymbol (fun x ↦ f (g * x)) hgf)
          - leftRegularOperator G g⁻¹ * φ (bddSymbol f hf)
            * star (leftRegularOperator G g⁻¹))).re|
        ≤ ‖coefficientAtOne (φ (bddSymbol (fun x ↦ f (g * x)) hgf)
            - leftRegularOperator G g⁻¹ * φ (bddSymbol f hf)
              * star (leftRegularOperator G g⁻¹))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ ‖φ (bddSymbol (fun x ↦ f (g * x)) hgf)
            - leftRegularOperator G g⁻¹ * φ (bddSymbol f hf)
              * star (leftRegularOperator G g⁻¹)‖ :=
          norm_coefficientAtOne_le _
      _ ≤ 2 * Real.sqrt (2 * (ε ^ 2 / 8)) * ‖bddSymbol f hf‖ := by
          rw [hsym]
          exact hest
      _ ≤ 2 * Real.sqrt (2 * (ε ^ 2 / 8)) * C := by
          refine mul_le_mul_of_nonneg_left
            (norm_bddSymbol_le f hf hC) (by positivity)
      _ = ε * C := by
          have hsq : 2 * (ε ^ 2 / 8) = (ε / 2) ^ 2 := by ring
          rw [hsq, Real.sqrt_sq (by positivity)]
          ring

end

end CStarExactness
end GroupApproximation
