import GroupApproximation.Manuscript.SimpleKazhdanSofic.ROmega.GroupGraph
import GroupApproximation.Analysis.GroupStandardFormInstance
import GroupApproximation.Analysis.ReducedGroupCStarSpan
import GroupApproximation.Analysis.PrintedUltrafilterHyperlinearTrace
import GroupApproximation.Analysis.MatrixUltraproductToHyperfiniteUltrapower
import GroupApproximation.Sofic.SoficPermutationTrace
import GroupApproximation.Meta.AxiomGuard

/-!
# `L(G) ↪ R^ω` for a countable sofic group

`simple_kazhdan_sofic_group.tex`, subsection "Brown's formulation":

> (tex 345–348) It is LEF, so it is sofic … and hyperlinear …, and $L(G)$ embeds in
> $\mathcal R^\omega$.

Route.  A sofic approximation `σₙ` with fixed-point counts tending to `[g = 1]` gives the unitary
representation `g ↦ [σₙ(g)]` of `G` in the matrix ultraproduct `∏ M_{dₙ}/ω`, whose ultratrace is
`[g = 1]` (`ShulmanTrace.soficUnitaryHomUltrafilter`), and the matrix ultraproduct maps
trace-preservingly into `R^ω` (`Hyperfinite.matrixUltraproductToHyperfiniteUltrapower`).  The pairs
`(λ(g), [σₙ(g)])` span a trace-compatible graph: the vector state of `δ₁` on `λ(g)` is `[g = 1]`
too, the first coordinates are `‖·δ₁‖`-dense in `L(G)` by the point-mass expansion, and `δ₁` is
separating.  `exists_injective_of_generators` extends the graph to an injective trace-preserving
`⋆`-homomorphism `L(G) → R^ω`.
-/

namespace GroupApproximation.SimpleKazhdanSofic.ROmega

open Filter TracialUltrapower ReducedGroupCStarTrace
open scoped InnerProductSpace Topology ENNReal

noncomputable section

section Operator

variable {G : Type} [Group G]

local instance romegaDecEqOperator : DecidableEq G := Classical.decEq G

/-- `δ₁` as a tracial vector of `L(G)`. -/
abbrev groupTracialVector (G : Type) [Group G] :
    TracialVector (GroupVonNeumann.groupVonNeumannAlgebra G) :=
  TracialVector.ofStandardForm (GroupVonNeumann.isTracialStandardForm G)

/-- The vector state of `δ₁` on `λ(g)` is `[g = 1]`. -/
theorem inner_deltaOne_leftRegularOperator (g : G) :
    ⟪deltaOne G, leftRegularOperator G g (deltaOne G)⟫_ℂ = if g = 1 then 1 else 0 := by
  rw [GroupVonNeumann.inner_deltaOne_left, GroupVonNeumann.leftRegularOperator_deltaOne]
  by_cases hg : g = 1
  · subst hg
    rw [if_pos rfl, lp.single_apply_self]
  · rw [if_neg hg, lp.single_apply_ne _ _ _ (Ne.symm hg)]

/-- Finite combinations of left translations are `‖·δ₁‖`-dense among all operators. -/
theorem exists_sum_leftRegularOperator_close (T : GroupHilbert G →L[ℂ] GroupHilbert G) {ε : ℝ}
    (hε : 0 < ε) : ∃ t : Finset G, ∃ c : G → ℂ,
      ‖(∑ g ∈ t, c g • leftRegularOperator G g - T) (deltaOne G)‖ < ε := by
  have htend : Tendsto
      (fun t : Finset G ↦ ∑ g ∈ t, (lp.single 2 g (T (deltaOne G) g) : GroupHilbert G))
      atTop (𝓝 (T (deltaOne G))) :=
    lp.hasSum_single ENNReal.ofNat_ne_top (T (deltaOne G))
  obtain ⟨t, ht⟩ := (htend.eventually_mem (Metric.ball_mem_nhds _ hε)).exists
  refine ⟨t, fun g ↦ T (deltaOne G) g, ?_⟩
  have hop : ∀ g ∈ t, (T (deltaOne G) g • leftRegularOperator G g) (deltaOne G)
      = (lp.single 2 g (T (deltaOne G) g) : GroupHilbert G) := fun g _ ↦ by
    rw [_root_.smul_apply, GroupVonNeumann.leftRegularOperator_deltaOne, ← lp.single_smul,
      smul_eq_mul, mul_one]
  rw [_root_.sub_apply, _root_.sum_apply, Finset.sum_congr rfl hop, ← dist_eq_norm]
  exact ht

end Operator

section Sofic

variable {G : Type} [Group G] (S : SoficApproximation G) [∀ n, Nonempty (S.model n)]
variable (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)

local instance romegaDecEqSofic : DecidableEq G := Classical.decEq G

/-- The sofic representation `g ↦ [σₙ(g)]`, landed in `R^ω`. -/
def soficHyperfinite (g : G) : Hyperfinite.HyperfiniteUltrapower ω :=
  Hyperfinite.matrixUltraproductToHyperfiniteUltrapower (fun n ↦ S.model n) ω hω
    ((ShulmanTrace.soficUnitaryHomUltrafilter S ω hω g :
      unitary (TracialUltraproduct.TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ))) :
      TracialUltraproduct.TracialMatrixQuotient (fun n ↦ S.model n) (ω : Filter ℕ))

theorem soficHyperfinite_one : soficHyperfinite S ω hω 1 = 1 := by
  rw [soficHyperfinite, map_one, Submonoid.coe_one, map_one]

theorem soficHyperfinite_mul (g h : G) :
    soficHyperfinite S ω hω (g * h) = soficHyperfinite S ω hω g * soficHyperfinite S ω hω h := by
  simp only [soficHyperfinite]
  rw [map_mul, Submonoid.coe_mul, map_mul]

theorem star_soficHyperfinite (g : G) :
    star (soficHyperfinite S ω hω g) = soficHyperfinite S ω hω g⁻¹ := by
  simp only [soficHyperfinite]
  rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star, map_star]

/-- The ultratrace of `[σₙ(g)]` in `R^ω` is `[g = 1]`. -/
theorem ultratrace_soficHyperfinite (hpos : ∀ n, 0 < Fintype.card (S.model n)) (g : G) :
    Hyperfinite.hyperfiniteUltratrace ω (soficHyperfinite S ω hω g) = if g = 1 then 1 else 0 := by
  rw [soficHyperfinite, Hyperfinite.ultratrace_matrixUltraproductToHyperfiniteUltrapower]
  by_cases hg : g = 1
  · subst hg
    rw [if_pos rfl, map_one, Submonoid.coe_one, TracialUltraproduct.ultratraceCLM_one]
  · rw [if_neg hg, ShulmanTrace.ultratraceCLM_soficUnitaryHomUltrafilter_eq_zero S ω hω hpos hg]

/-- The generator pairs `(λ(g), [σₙ(g)])`. -/
def groupPair (g : G) :
    (GroupHilbert G →L[ℂ] GroupHilbert G) × Hyperfinite.HyperfiniteUltrapower ω :=
  (leftRegularOperator G g, soficHyperfinite S ω hω g)

theorem groupPair_mem_span (g : G) :
    groupPair S ω hω g ∈ Submodule.span ℂ (Set.range (groupPair S ω hω)) :=
  Submodule.subset_span ⟨g, rfl⟩

theorem groupPair_one_mem :
    (1 : (GroupHilbert G →L[ℂ] GroupHilbert G) × Hyperfinite.HyperfiniteUltrapower ω)
      ∈ Submodule.span ℂ (Set.range (groupPair S ω hω)) := by
  have h : groupPair S ω hω 1 = 1 :=
    Prod.ext (leftRegularOperator_one G) (soficHyperfinite_one S ω hω)
  rw [← h]
  exact groupPair_mem_span S ω hω 1

theorem groupPair_mul_mem (g h : G) :
    groupPair S ω hω g * groupPair S ω hω h ∈ Submodule.span ℂ (Set.range (groupPair S ω hω)) := by
  have e : groupPair S ω hω g * groupPair S ω hω h = groupPair S ω hω (g * h) :=
    Prod.ext (leftRegularOperator_mul G g h) (soficHyperfinite_mul S ω hω g h).symm
  rw [e]
  exact groupPair_mem_span S ω hω (g * h)

theorem groupPair_star_mem (g : G) :
    star (groupPair S ω hω g) ∈ Submodule.span ℂ (Set.range (groupPair S ω hω)) := by
  have e : star (groupPair S ω hω g) = groupPair S ω hω g⁻¹ :=
    Prod.ext (GroupVonNeumann.star_leftRegularOperator G g) (star_soficHyperfinite S ω hω g)
  rw [e]
  exact groupPair_mem_span S ω hω g⁻¹

theorem groupPair_trace (hpos : ∀ n, 0 < Fintype.card (S.model n)) (g : G) :
    ultratrace Hyperfinite.hyperfiniteTracialVector ω (groupPair S ω hω g).2
      = ⟪(groupTracialVector G).vec, (groupPair S ω hω g).1 (groupTracialVector G).vec⟫_ℂ :=
  (ultratrace_soficHyperfinite S ω hω hpos g).trans (inner_deltaOne_leftRegularOperator g).symm

end Sofic

/-- **`L(G) ↪ R^ω`** (tex 345–348): for a countable sofic group `G` and a free ultrafilter `ω`,
there is an injective `⋆`-homomorphism from `L(G)` into `R^ω` carrying the canonical trace of `L(G)`
to the ultratrace. -/
theorem exists_groupVonNeumann_embedding {G : Type} [Group G] [Countable G] (hG : IsSofic G)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    ∃ Φ : ↥(GroupVonNeumann.groupVonNeumannAlgebra G).toStarSubalgebra →⋆ₐ[ℂ]
        Hyperfinite.HyperfiniteUltrapower ω, Function.Injective Φ ∧
      ∀ T : ↥(GroupVonNeumann.groupVonNeumannAlgebra G).toStarSubalgebra,
        Hyperfinite.hyperfiniteUltratrace ω (Φ T)
          = ⟪deltaOne G, (T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)⟫_ℂ := by
  obtain ⟨S, hpos, -, -⟩ := SoficPermutationTrace.exists_soficApproximation_tendsto_normTrace hG
  haveI : ∀ n, Nonempty (S.model n) := fun n ↦ Fintype.card_pos_iff.mp (hpos n)
  obtain ⟨Φ, hinj, htr, -⟩ := exists_injective_of_generators (groupTracialVector G)
    (groupPair S ω hω) (groupPair_one_mem S ω hω) (groupPair_mul_mem S ω hω)
    (groupPair_star_mem S ω hω) hω (fun g ↦ GroupVonNeumann.leftRegularOperator_mem G g)
    (groupPair_trace S ω hω hpos)
    (fun T _ ε hε ↦ exists_sum_leftRegularOperator_close T hε)
    (fun T hT h ↦ (GroupVonNeumann.isTracialStandardForm G).separating T hT h)
  exact ⟨Φ, hinj, htr⟩

end

end GroupApproximation.SimpleKazhdanSofic.ROmega

#audit_axioms GroupApproximation.SimpleKazhdanSofic.ROmega.exists_groupVonNeumann_embedding
