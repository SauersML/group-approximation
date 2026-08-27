import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaEvaluatedCornerStable

/-! # Coordinate evaluation of the canonical Ueda corner map -/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

/-- The corner composite, taken through a SINGLE `CStarAlgebra` binder.

`cStarUpperLeftCornerMap.comp f` written directly at `f := R.base` cannot
elaborate: `StarAlgHom.comp` carries separate `[Semiring A] [Algebra ℂ A]
[Star A]` binders, the `Semiring` is fixed by unification with `R.base`'s type
(the `[CStarAlgebra D]` path of the `UniversalCStarHNN` section), and the
`Algebra ℂ A` search then has to return a term over exactly that `Semiring`,
which it does not.  Routing through one `[CStarAlgebra E]` binder unifies the
whole structure with `baseAlgebraCStarAlgebra data` in one step — the same
reason `matrixTwoMap R.base` works in `EvaluatedFactorDefs`. -/
def cornerComp {E K : Type} [CStarAlgebra E] [CStarAlgebra K]
    (f : E →⋆ₐ[ℂ] K) :
    E →⋆ₐ[ℂ]
      CStarCorner (cStarUpperLeftCornerUnit (K := K))
        (cStarUpperLeftCornerUnit_star (K := K))
        (cStarUpperLeftCornerUnit_mul (K := K)) :=
  cStarUpperLeftCornerMap.comp f

@[simp] theorem cornerComp_apply {E K : Type} [CStarAlgebra E]
    [CStarAlgebra K] (f : E →⋆ₐ[ℂ] K) (x : E) :
    cornerComp f x = cStarUpperLeftCornerMap (f x) :=
  rfl

variable (data : CoronaConjugator G S T phi A X)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Coordinate evaluation of the Ueda corner map.

Three things this proof has to supply that the elaborator cannot find on its
own.  The two `Semiring` searches in the statement run over the `lp` behind
`universalHNN`, so they need the budget.  The composite with `R.base` goes
through `cornerComp`, for the reason recorded there.  And the corner of
`M₂(R.carrier)` is nontrivial because `cStarUpperLeftCornerMap` is injective
and `R.carrier` is nontrivial; that is a fact, not a search. -/
theorem evaluatedCornerMap_comp_uedaCornerMap
    (hUeda : UedaCornerMapStatement) (R : HNNCoordinate data) :
    (evaluatedCornerMap data R).comp (uedaCornerMap hUeda data) =
      cStarUpperLeftCornerMap.comp
        (universalCStarHNNEval (sourceEdgeAlgebra data)
          (targetEdgeAlgebra data) (edgeIsomorphism data) R) := by
  haveI : Nontrivial (CStarCorner (cStarUpperLeftCornerUnit (K := R.carrier))
      (cStarUpperLeftCornerUnit_star (K := R.carrier))
      (cStarUpperLeftCornerUnit_mul (K := R.carrier))) :=
    ⟨⟨cStarUpperLeftCornerMap (1 : R.carrier),
      cStarUpperLeftCornerMap (0 : R.carrier),
      fun h ↦ one_ne_zero (cStarUpperLeftCornerMap_injective h)⟩⟩
  refine (universalCStarHNN_existsUnique_lift
    (sourceEdgeAlgebra data) (targetEdgeAlgebra data) (edgeIsomorphism data)
    (cornerComp R.base)
    (unitaryMapOfStarAlgHom cStarUpperLeftCornerMap R.stable)
    (fun b ↦ by
      have h := congrArg (cStarUpperLeftCornerMap (K := R.carrier))
        (R.covariance b)
      simpa [cornerComp_apply, coe_unitaryMapOfStarAlgHom, map_mul]
        using h)).unique ?_ ?_
  · constructor
    · intro d
      have h : universalCStarHNNBase (sourceEdgeAlgebra data)
            (targetEdgeAlgebra data) (edgeIsomorphism data) d =
          universalBase data d := rfl
      rw [h, StarAlgHom.comp_apply, uedaCornerMap_base, evaluatedCornerMap_base,
        cornerComp_apply]
    · have h : ((universalCStarHNNStable (sourceEdgeAlgebra data)
            (targetEdgeAlgebra data) (edgeIsomorphism data) :
          unitary (universalHNN data)) : universalHNN data) =
          ((universalStable data : unitary (universalHNN data)) :
            universalHNN data) := rfl
      rw [h, StarAlgHom.comp_apply, uedaCornerMap_stable, evaluatedCornerMap_stable,
        coe_unitaryMapOfStarAlgHom]
  · constructor
    · intro d
      simp
    · simp

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
