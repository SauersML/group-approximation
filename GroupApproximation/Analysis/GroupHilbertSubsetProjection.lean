import GroupApproximation.Analysis.LanceMultiplicationOperator
import GroupApproximation.Meta.AxiomGuard

/-!
# Coordinate projections of `ℓ²(G)`

For a subset `S ⊆ G` let `P_S` be multiplication by the indicator of `S`, a
bounded operator on `ℓ²(G)`.  Nothing new is built: `P_S` is the landed
multiplication operator `CStarExactness.mulOp` of
`Analysis/LanceMultiplicationOperator` at the indicator symbol, and every fact
below is one of that module's lemmas plus a computation with indicators.  What
this module adds is the *projection algebra*, in the non-dependent form Powers'
averaging argument needs — `mulOp` carries its norm bound and the bound's proof
as arguments, so `mulOp f C h` at two different bounds is two different terms,
and `mulOp_congr_of_symbol_eq` is what lets the identities below be stated at all.

* `subsetProjection_apply` — the formula;
* `subsetProjection_idem`, `subsetProjection_star` — `P_S` is a projection;
* `subsetProjection_mul` — `P_S P_T = P_{S ∩ T}`, hence
  `subsetProjection_mul_of_disjoint`, `P_S P_T = 0` for disjoint `S`, `T`;
* `subsetProjection_univ` — `P_G = 1`;
* `leftRegularOperator_conj_subsetProjection` — `λ(g) P_S λ(g)⋆ = P_{gS}`, the
  equivariance that makes the family `{P_{gᵢ D}}` orthogonal when the translates
  `gᵢ D` are pairwise disjoint;
* `norm_subsetProjection_le_one`.

## Why these are the right facts

Powers' estimate splits an element `a` of the reduced C⋆-algebra with support in
`F ⊆ G \ {1}` along a partition `G = C ⊔ D` chosen so that `f C ∩ C = ∅` for
every `f ∈ F`.  That choice makes `P_C a P_C = 0`, so

    a = P_D a P_C + a P_D,

and averaging by `λ(g₁), …, λ(gₙ)` turns each summand into a sum `∑ᵢ Aᵢ Qᵢ` (or
`∑ᵢ Qᵢ Bᵢ`) with `Qᵢ = P_{gᵢ D}` pairwise orthogonal.  The norm of such a sum is
at most `√n · max ‖Aᵢ‖` — that is the landed estimate
`ShulmanFill.norm_sum_sq_le_of_almostOrthogonal` at off-diagonal size `δ = 0`,
whose hypothesis `‖Gᵢ (G_j)⋆‖ ≤ 0` is exactly `Qᵢ Q_j = 0`.

**None of these projections lies in `C*_r(G)`**, and none has to: the whole
estimate happens in `B(ℓ²G)`, where the reduced algebra sits isometrically as a
star subalgebra.

## Manuscript status

Infrastructure for `cor:regular-nonmf-algebra` (Powers' averaging estimate);
certifies no printed sentence on its own.
-/

namespace GroupApproximation
namespace ReducedGroupCStarTrace

open GroupApproximation.GroupVonNeumann GroupApproximation.CStarExactness
open scoped Pointwise

universe u

noncomputable section

/-! ## The indicator symbol

No group structure is used here, so the section variables are the bare type. -/

section Indicator

variable (G : Type u)

/-- The indicator of `S`, as a symbol on `G`. -/
def indicatorSymbol (S : Set G) : G → ℂ := S.indicator (fun _ ↦ (1 : ℂ))

theorem indicatorSymbol_of_mem {S : Set G} {g : G} (h : g ∈ S) :
    indicatorSymbol G S g = 1 := Set.indicator_of_mem h _

theorem indicatorSymbol_of_notMem {S : Set G} {g : G} (h : g ∉ S) :
    indicatorSymbol G S g = 0 := Set.indicator_of_notMem h _

theorem norm_indicatorSymbol_le (S : Set G) (g : G) :
    ‖indicatorSymbol G S g‖ ≤ 1 := by
  by_cases h : g ∈ S
  · rw [indicatorSymbol_of_mem G h, norm_one]
  · rw [indicatorSymbol_of_notMem G h, norm_zero]
    exact zero_le_one

end Indicator

variable (G : Type u) [Group G]

/-! ## Multiplication operators with equal symbols agree -/

/-- **Two multiplication operators with the same symbol are equal**, whatever
norm bounds they were built with.  `mulOp` takes the bound and its proof as
arguments, so this is not `rfl`; it is what makes the projection identities
below statable. -/
theorem mulOp_congr_of_symbol_eq {f₁ f₂ : G → ℂ} {C₁ C₂ : ℝ} (h₁ : ∀ g, ‖f₁ g‖ ≤ C₁)
    (h₂ : ∀ g, ‖f₂ g‖ ≤ C₂) (hf : ∀ g, f₁ g = f₂ g) :
    mulOp f₁ C₁ h₁ = mulOp f₂ C₂ h₂ := by
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  rw [mulOp_apply, mulOp_apply, hf g]

/-! ## The projection -/

/-- **The coordinate projection of `ℓ²(G)` onto `S`**: multiplication by the
indicator function of `S`. -/
def subsetProjection (S : Set G) : GroupHilbert G →L[ℂ] GroupHilbert G :=
  mulOp (indicatorSymbol G S) 1 (norm_indicatorSymbol_le G S)

@[simp] theorem subsetProjection_apply (S : Set G) (x : GroupHilbert G) (g : G) :
    (subsetProjection G S x : GroupHilbert G) g = indicatorSymbol G S g * x g := rfl

theorem norm_subsetProjection_le_one (S : Set G) : ‖subsetProjection G S‖ ≤ 1 :=
  norm_mulOp_le _ _ _

/-! ## The projection identities -/

/-- **`P_S P_T = P_{S ∩ T}`.** -/
theorem subsetProjection_mul (S T : Set G) :
    subsetProjection G S * subsetProjection G T = subsetProjection G (S ∩ T) := by
  have hprod : ∀ g : G,
      ‖indicatorSymbol G S g * indicatorSymbol G T g‖ ≤ 1 * 1 := by
    intro g
    rw [norm_mul]
    exact mul_le_mul (norm_indicatorSymbol_le G S g) (norm_indicatorSymbol_le G T g)
      (norm_nonneg _) zero_le_one
  have hcomp := mulOp_comp (indicatorSymbol G S) (indicatorSymbol G T) 1 1
    (norm_indicatorSymbol_le G S) (norm_indicatorSymbol_le G T) hprod
  have hsym : ∀ g : G, indicatorSymbol G S g * indicatorSymbol G T g
      = indicatorSymbol G (S ∩ T) g := by
    intro g
    by_cases hS : g ∈ S
    · by_cases hT : g ∈ T
      · rw [indicatorSymbol_of_mem G hS, indicatorSymbol_of_mem G hT,
          indicatorSymbol_of_mem G (Set.mem_inter hS hT), one_mul]
      · rw [indicatorSymbol_of_notMem G hT,
          indicatorSymbol_of_notMem G
            (fun hmem ↦ hT (Set.mem_of_mem_inter_right hmem)), mul_zero]
    · rw [indicatorSymbol_of_notMem G hS,
        indicatorSymbol_of_notMem G
          (fun hmem ↦ hS (Set.mem_of_mem_inter_left hmem)), zero_mul]
  calc subsetProjection G S * subsetProjection G T
      = mulOp (indicatorSymbol G S) 1 (norm_indicatorSymbol_le G S) ∘L
          mulOp (indicatorSymbol G T) 1 (norm_indicatorSymbol_le G T) :=
        ContinuousLinearMap.mul_def _ _
    _ = mulOp (fun g ↦ indicatorSymbol G S g * indicatorSymbol G T g) (1 * 1) hprod :=
        hcomp.symm
    _ = subsetProjection G (S ∩ T) :=
        mulOp_congr_of_symbol_eq G hprod (norm_indicatorSymbol_le G (S ∩ T)) hsym

/-- **`P_S` is idempotent.** -/
theorem subsetProjection_idem (S : Set G) :
    subsetProjection G S * subsetProjection G S = subsetProjection G S := by
  rw [subsetProjection_mul, Set.inter_self]

/-- **Disjoint subsets give orthogonal projections.** -/
theorem subsetProjection_mul_of_disjoint {S T : Set G} (h : Disjoint S T) :
    subsetProjection G S * subsetProjection G T = 0 := by
  rw [subsetProjection_mul]
  refine ContinuousLinearMap.ext fun x ↦ lp.ext (funext fun g ↦ ?_)
  rw [subsetProjection_apply,
    indicatorSymbol_of_notMem G
      (fun hg : g ∈ S ∩ T ↦ Set.disjoint_left.mp h
        (Set.mem_of_mem_inter_left hg) (Set.mem_of_mem_inter_right hg)),
    zero_mul]
  simp

/-- **`P_G = 1`.** -/
theorem subsetProjection_univ : subsetProjection G (Set.univ : Set G) = 1 := by
  have hone : ∀ g : G, ‖(1 : ℂ)‖ ≤ 1 := fun _ ↦ by norm_num
  calc subsetProjection G (Set.univ : Set G)
      = mulOp (fun _ : G ↦ (1 : ℂ)) 1 hone :=
        mulOp_congr_of_symbol_eq G (norm_indicatorSymbol_le G Set.univ) hone
          (fun g ↦ indicatorSymbol_of_mem G (Set.mem_univ g))
    _ = 1 := mulOp_one

/-! ## Self-adjointness -/

/-- **`P_S` is self-adjoint.** -/
theorem subsetProjection_star (S : Set G) :
    star (subsetProjection G S) = subsetProjection G S := by
  have hconj : ∀ g : G, ‖(starRingEnd ℂ) (indicatorSymbol G S g)‖ ≤ 1 := by
    intro g
    simpa using norm_indicatorSymbol_le G S g
  rw [subsetProjection, star_mulOp]
  refine mulOp_congr_of_symbol_eq G hconj (norm_indicatorSymbol_le G S) fun g ↦ ?_
  by_cases h : g ∈ S
  · rw [indicatorSymbol_of_mem G h, map_one]
  · rw [indicatorSymbol_of_notMem G h, map_zero]

/-! ## Equivariance -/

/-- Membership in a left translate of a subset of the group. -/
theorem mem_smul_set_group (g x : G) (S : Set G) : x ∈ g • S ↔ g⁻¹ * x ∈ S := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

/-- **`λ(g) P_S λ(g)⋆ = P_{gS}`.**

This is the only place where the group acts: translating the indicator of `S` by
`g` gives the indicator of `gS`.  It is what makes the translates `gᵢ D` of a
single set give *orthogonal* projections when they are pairwise disjoint. -/
theorem leftRegularOperator_conj_subsetProjection (g : G) (S : Set G) :
    leftRegularOperator G g * subsetProjection G S *
        star (leftRegularOperator G g) = subsetProjection G (g • S) := by
  have htrans : ∀ h : G, ‖indicatorSymbol G S (g⁻¹ * h)‖ ≤ 1 :=
    fun h ↦ norm_indicatorSymbol_le G S (g⁻¹ * h)
  have hcov := leftRegular_conj_mulOp g (indicatorSymbol G S) 1
    (norm_indicatorSymbol_le G S)
  have hassoc : leftRegularOperator G g * subsetProjection G S *
      star (leftRegularOperator G g)
      = leftRegularOperator G g ∘L subsetProjection G S ∘L
        leftRegularOperator G g⁻¹ := by
    rw [star_leftRegularOperator, mul_assoc]
    rfl
  rw [hassoc, subsetProjection, hcov]
  refine mulOp_congr_of_symbol_eq G htrans (norm_indicatorSymbol_le G (g • S)) fun h ↦ ?_
  by_cases hx : g⁻¹ * h ∈ S
  · rw [indicatorSymbol_of_mem G hx,
      indicatorSymbol_of_mem G ((mem_smul_set_group G g h S).mpr hx)]
  · rw [indicatorSymbol_of_notMem G hx,
      indicatorSymbol_of_notMem G (fun hc ↦ hx ((mem_smul_set_group G g h S).mp hc))]

end

end ReducedGroupCStarTrace
end GroupApproximation

open GroupApproximation.ReducedGroupCStarTrace

#audit_axioms subsetProjection
#audit_axioms subsetProjection_mul
#audit_axioms subsetProjection_idem
#audit_axioms subsetProjection_mul_of_disjoint
#audit_axioms subsetProjection_star
#audit_axioms subsetProjection_univ
#audit_axioms norm_subsetProjection_le_one
#audit_axioms leftRegularOperator_conj_subsetProjection
