import GroupApproximation.Analysis.MaximalGroupCStar
import GroupApproximation.Analysis.ReducedGroupCStarSeparable
import GroupApproximation.Analysis.ReducedGroupCStarTraceFaithful

/-!
# The canonical trace on the maximal group C-star algebra

`Analysis.MaximalGroupCStar` builds the universe-relative maximal group
C-star algebra together with the evaluation map at any same-universe unitary
representation.  Evaluating at the concrete left regular representation gives
the canonical map

`q : C*(G) → C*_r(G)`,

and `Analysis.ReducedGroupCStarTraceFaithful` supplies the canonical faithful
trace `τ_r` on the target.  This file composes them into the canonical trace

`τ_G = τ_r ∘ q : C*(G) → ℂ`

and proves the single structural fact the rest of the development consumes,

`τ_G (u_g) = if g = 1 then 1 else 0`,

together with the tracial-state properties of `τ_G`: it is normalized,
positive on elements `a⋆ a`, hermitian, and invariant under swapping the
factors of a product.  Finally, the separability argument already used for the
reduced algebra is adapted to the maximal algebra, which needs only that its
generating set is countable.

Faithfulness is deliberately *not* claimed: `q` has a kernel unless `G` is
amenable, and that is exactly why `τ_G` is interesting.
-/

open scoped CStarAlgebra ComplexOrder ENNReal InnerProductSpace Pointwise

namespace GroupApproximation

noncomputable section

universe u

namespace ReducedGroupCStarTrace

variable (G : Type u) [Group G]

/-- The point-mass lemmas quantify over a decidable equality on the group.
This is the same classical instance that `Analysis.ReducedGroupCStarTrace` and
its neighbours install, so the instance argument buried inside `lp.single`
matches theirs syntactically and the point-mass rewrites fire. -/
local instance canonicalMaximalTraceDecidableEq : DecidableEq G :=
  Classical.decEq G

/-- The canonical reduced coefficient is normalized. -/
theorem canonicalCoefficientAtOne_one :
    canonicalCoefficientAtOne G (1 : ReducedGroupCStar G) = 1 := by
  change ((1 : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1 = 1
  simp [deltaOne]

/-- The canonical reduced coefficient is the matrix coefficient of the
identity vector. -/
theorem canonicalCoefficientAtOne_eq_inner (T : ReducedGroupCStar G) :
    canonicalCoefficientAtOne G T =
      ⟪deltaOne G,
        (T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)⟫_ℂ := by
  change ((T : GroupHilbert G →L[ℂ] GroupHilbert G) (deltaOne G)) 1 = _
  rw [deltaOne, lp.inner_single_left]
  simp

/-- The canonical reduced coefficient is hermitian. -/
theorem canonicalCoefficientAtOne_star (T : ReducedGroupCStar G) :
    canonicalCoefficientAtOne G (star T) =
      starRingEnd ℂ (canonicalCoefficientAtOne G T) := by
  rw [canonicalCoefficientAtOne_eq_inner G (star T),
    canonicalCoefficientAtOne_eq_inner G T]
  change ⟪deltaOne G,
    (star (T : GroupHilbert G →L[ℂ] GroupHilbert G)) (deltaOne G)⟫_ℂ = _
  rw [ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

/-- The canonical reduced coefficient vanishes on every nonidentity left
regular unitary: its identity column is the point mass at `g`. -/
theorem canonicalCoefficientAtOne_reducedLeftRegular_of_ne_one {g : G}
    (hg : g ≠ 1) : canonicalCoefficientAtOne G (reducedLeftRegular G g) = 0 := by
  change ((reducedLeftRegular G g : GroupHilbert G →L[ℂ] GroupHilbert G)
    (deltaOne G)) 1 = 0
  rw [reducedLeftRegular_deltaOne, lp.coeFn_single,
    Pi.single_eq_of_ne (Ne.symm hg)]

end ReducedGroupCStarTrace

open ReducedGroupCStarTrace

variable (G : Type u) [Group G]

/-- The canonical map from the maximal group C-star algebra to the concrete
reduced group C-star algebra: evaluation of the universal diagonal
representation at the left regular coordinate. -/
def maximalGroupCStarToReduced :
    MaximalGroupCStar G →⋆ₐ[ℂ] ReducedGroupCStar G :=
  maximalGroupCStarEval G (CStarUnitaryRepresentation.reduced G)

@[simp] theorem maximalGroupCStarToReduced_generator (g : G) :
    maximalGroupCStarToReduced G (maximalGroupCStarGenerator G g) =
      reducedLeftRegular G g :=
  rfl

/-- The canonical trace on the maximal group C-star algebra: the canonical
faithful trace of the reduced algebra, pulled back along the canonical map. -/
def canonicalMaximalTrace : MaximalGroupCStar G →L[ℂ] ℂ where
  toFun a := canonicalCoefficientAtOne G (maximalGroupCStarToReduced G a)
  map_add' a b := by simp
  map_smul' c a := by simp
  cont := (canonicalCoefficientAtOne G).continuous.comp
    (map_continuous (maximalGroupCStarToReduced G))

/-- The defining factorization `τ_G = τ_r ∘ q`. -/
@[simp] theorem canonicalMaximalTrace_apply (a : MaximalGroupCStar G) :
    canonicalMaximalTrace G a =
      canonicalCoefficientAtOne G (maximalGroupCStarToReduced G a) :=
  rfl

/-- The canonical trace is normalized. -/
theorem canonicalMaximalTrace_one : canonicalMaximalTrace G 1 = 1 := by
  rw [canonicalMaximalTrace_apply, map_one, canonicalCoefficientAtOne_one]

/-- The canonical trace of the identity generator. -/
theorem canonicalMaximalTrace_generator_one :
    canonicalMaximalTrace G (maximalGroupCStarGenerator G 1) = 1 := by
  rw [canonicalMaximalTrace_apply, maximalGroupCStarToReduced_generator,
    reducedLeftRegular_one, canonicalCoefficientAtOne_one]

/-- The canonical trace kills every nonidentity generator. -/
theorem canonicalMaximalTrace_generator_of_ne_one {g : G} (hg : g ≠ 1) :
    canonicalMaximalTrace G (maximalGroupCStarGenerator G g) = 0 := by
  rw [canonicalMaximalTrace_apply, maximalGroupCStarToReduced_generator,
    canonicalCoefficientAtOne_reducedLeftRegular_of_ne_one G hg]

/-- **The generator formula.**  The canonical trace of the canonical generator
`u_g` is `1` at the identity and `0` everywhere else. -/
theorem canonicalMaximalTrace_generator (g : G) [Decidable (g = 1)] :
    canonicalMaximalTrace G (maximalGroupCStarGenerator G g) =
      if g = 1 then 1 else 0 := by
  by_cases hg : g = 1
  · rw [if_pos hg, hg]
    exact canonicalMaximalTrace_generator_one G
  · rw [if_neg hg]
    exact canonicalMaximalTrace_generator_of_ne_one G hg

/-- The generator formula, stated for the canonical unitary representation of
the group inside its maximal C-star algebra. -/
theorem canonicalMaximalTrace_unitaryHom (g : G) [Decidable (g = 1)] :
    canonicalMaximalTrace G
        ((maximalGroupCStarUnitaryHom G g : unitary (MaximalGroupCStar G)) :
          MaximalGroupCStar G) =
      if g = 1 then 1 else 0 :=
  canonicalMaximalTrace_generator G g

/-- The canonical trace is positive. -/
theorem canonicalMaximalTrace_star_mul_self_nonneg (a : MaximalGroupCStar G) :
    0 ≤ canonicalMaximalTrace G (star a * a) := by
  rw [canonicalMaximalTrace_apply, map_mul, map_star,
    canonicalCoefficientAtOne_star_mul_self]
  positivity

/-- The canonical trace is hermitian. -/
theorem canonicalMaximalTrace_star (a : MaximalGroupCStar G) :
    canonicalMaximalTrace G (star a) =
      starRingEnd ℂ (canonicalMaximalTrace G a) := by
  rw [canonicalMaximalTrace_apply, canonicalMaximalTrace_apply, map_star,
    canonicalCoefficientAtOne_star]

/-- The canonical trace is tracial. -/
theorem canonicalMaximalTrace_mul_comm (a b : MaximalGroupCStar G) :
    canonicalMaximalTrace G (a * b) = canonicalMaximalTrace G (b * a) := by
  rw [canonicalMaximalTrace_apply, canonicalMaximalTrace_apply,
    map_mul (maximalGroupCStarToReduced G) a b,
    map_mul (maximalGroupCStarToReduced G) b a,
    canonicalCoefficientAtOne_mul_comm G (maximalGroupCStarToReduced G a)
      (maximalGroupCStarToReduced G b)]

/-- **The canonical trace is a tracial state**: normalized, positive, and
invariant under swapping the factors of a product. -/
theorem canonicalMaximalTrace_isTracialState :
    canonicalMaximalTrace G 1 = 1 ∧
      (∀ a : MaximalGroupCStar G, 0 ≤ canonicalMaximalTrace G (star a * a)) ∧
      (∀ a b : MaximalGroupCStar G,
        canonicalMaximalTrace G (a * b) = canonicalMaximalTrace G (b * a)) :=
  ⟨canonicalMaximalTrace_one G, canonicalMaximalTrace_star_mul_self_nonneg G,
    canonicalMaximalTrace_mul_comm G⟩

/-- The maximal group C-star algebra of a countable group is separable: it is
the norm closure of the star algebra generated by the countable set of
canonical generators.  The ambient bounded product is *not* separable, so the
argument is the one already used for the reduced algebra. -/
theorem maximalGroupCStar_separableSpace [Countable G] :
    TopologicalSpace.SeparableSpace (MaximalGroupCStar G) := by
  let A := MaximalGroupCStarAmbient G
  let s : Set A := Set.range (fun g : G ↦
    (maximalGroupCStarAmbientRepresentation G g : MaximalGroupCStarAmbient G))
  have hs : s.Countable := Set.countable_range _
  have hsStar : (star s : Set A).Countable := by
    rw [← Set.image_star]
    exact hs.image _
  let t : Set A := s ∪ star s
  have ht : t.Countable := by
    simpa [t] using hs.union hsStar
  letI : Countable ↥t := ht.to_subtype
  have hmonoid :
      ((Submonoid.closure t : Submonoid A) : Set A).Countable := by
    rw [Submonoid.closure_eq_mrange, MonoidHom.coe_mrange]
    exact Set.countable_range _
  have hadjoin :
      TopologicalSpace.IsSeparable
        ((StarAlgebra.adjoin ℂ s : StarSubalgebra ℂ A) : Set A) := by
    change TopologicalSpace.IsSeparable
      ((StarAlgebra.adjoin ℂ s).toSubalgebra.toSubmodule : Set A)
    rw [StarAlgebra.adjoin_eq_span]
    simpa [t] using hmonoid.isSeparable.span
  have hclosed : TopologicalSpace.IsSeparable
      ((maximalGroupCStarSubalgebra G : StarSubalgebra ℂ A) : Set A) := by
    change TopologicalSpace.IsSeparable
      (((StarAlgebra.adjoin ℂ s).topologicalClosure :
        StarSubalgebra ℂ A) : Set A)
    rw [StarSubalgebra.topologicalClosure_coe]
    exact hadjoin.closure
  exact hclosed.separableSpace

end

end GroupApproximation
