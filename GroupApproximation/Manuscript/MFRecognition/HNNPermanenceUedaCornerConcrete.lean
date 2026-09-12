import GroupApproximation.Manuscript.MFRecognition.HNNPermanenceUedaCornerProof

/-!
# Ueda's corner map, with every implicit pinned

`HNNPermanenceUedaCornerProof` builds the corner map by applying its abstract
`cornerLift` to the algebras of a `CoronaConjugator` and letting unification
find the seven implicit arguments.  That application is the one place in the
corpus where the elaborator must see through `amalgam data`: the packaged
carrier is a `PackagedCStarAlgebra` built by a tactic with a `letI`, and
`cornerLift` asks for its argument at `UniversalCStarAmalgam iA iB`, so
`↥(amalgam data) =?= UniversalCStarAmalgam ?iA ?iB` has to be solved with
metavariables on the right.

This module states the same instantiation with `B0`, `B1`, `theta`, `iA` and
`iB` supplied by name.  The construction is identical -- the two lifts are the
same term -- but no metavariable is ever solved through the package: once
`iA` and `iB` are given, the expected type of `e` is ground, and accepting
`cornerUnit data` is a closed definitional check that `whnf` discharges by
unfolding `amalgam`, zeta-reducing its `letI`, and projecting.  The two
`Nonempty` arguments are `Prop`-valued, so the instance frozen inside
`amalgam data` and the one typeclass search returns agree by proof
irrelevance and never have to be compared structurally.

Two things this module deliberately does not do.

It does not rebuild the lift concretely, coordinate by coordinate, out of
`HNNPermanenceUedaCoordinateCorner`.  That module does produce the coordinate
covariant representation directly at `Type 0` -- it is the concrete twin of
`cornerCoordinateHNN` -- but it does not help here.  The conclusion of
`UedaCornerMapStatement` is a map into `CStarCorner (cornerUnit data) …`,
whose ambient is the packaged amalgam, so the package boundary has to be
crossed by any proof whatever; and assembling the lift concretely would in
addition demand the multiplication, star, unit and algebra structure of
`UniversalCStarAmalgamAmbient (amalgamLeftInclusion data)
(amalgamRightInclusion data)` at the concrete matrix algebras, which is
exactly the typeclass budget the abstract/concrete split exists to avoid.
The concrete route is strictly more expensive, not less.

It is also not independent of the module it backs up: the abstract API it
instantiates lives in `HNNPermanenceUedaCornerProof` alongside the
instantiation it is meant to replace, so a failure there takes this module
down too.  Moving that file's `section Abstract` into its own module under
`Analysis` is what would turn this into a real fallback; until then this is a
drop-in replacement text for that file's `uedaCornerLift`, kept compiling
beside it rather than instead of it.

The declarations below are deliberate near-duplicates of that file's
instantiation section, carrying a `Pinned` suffix so that both can be
imported at once.  Neither `uedaCornerLiftPinned_base` nor
`_stable` is a `simp` lemma: their unpinned twins already are, and the pair
would only give `simp` two ways to do one rewrite.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace HNNPermanence

noncomputable section

variable {G : Type} [Group G] {S T : Subgroup G} {phi : S ≃* T}
variable {A : Type} [CStarAlgebra A]
variable {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]

variable (data : CoronaConjugator G S T phi A X)

/-- Printed Step 1, with the amalgam datum pinned: the covariant pair
`(d ↦ diag(d,0), e₁₂f₂₁)` in `ePe` induces a star-algebra homomorphism
`U → ePe`.  Same term as `uedaCornerLift`; only the elaboration differs. -/
def uedaCornerLiftPinned : universalHNN data →⋆ₐ[ℂ]
    CStarCorner (cornerUnit data) (cornerUnit_star data)
      (cornerUnit_mul data) :=
  cornerLift
    (B0 := sourceEdgeAlgebra data) (B1 := targetEdgeAlgebra data)
    (theta := edgeIsomorphism data)
    (iA := amalgamLeftInclusion data) (iB := amalgamRightInclusion data)
    (e := cornerUnit data) (he_star := cornerUnit_star data)
    (he_mul := cornerUnit_mul data) (pi := cornerBaseMap data)
    (u := cornerStableUnitary data)
    (hcov := cornerStableUnitary_covariance data)
    (hne := cornerUnit_cornerProjectionAt_ne_zero data)

/-- The pinned lift carries the base algebra to Ueda's corner base map. -/
theorem uedaCornerLiftPinned_base (d : baseAlgebra data) :
    uedaCornerLiftPinned data (universalBase data d) = cornerBaseMap data d :=
  cornerLift_base
    (B0 := sourceEdgeAlgebra data) (B1 := targetEdgeAlgebra data)
    (theta := edgeIsomorphism data)
    (iA := amalgamLeftInclusion data) (iB := amalgamRightInclusion data)
    (e := cornerUnit data) (he_star := cornerUnit_star data)
    (he_mul := cornerUnit_mul data) (pi := cornerBaseMap data)
    (u := cornerStableUnitary data)
    (hcov := cornerStableUnitary_covariance data)
    (hne := cornerUnit_cornerProjectionAt_ne_zero data) d

/-- The pinned lift carries the stable unitary to Ueda's corner word. -/
theorem uedaCornerLiftPinned_stable :
    uedaCornerLiftPinned data
        ((universalStable data : unitary (universalHNN data)) :
          universalHNN data) =
      (cornerStableUnitary data :
        CStarCorner (cornerUnit data) (cornerUnit_star data)
          (cornerUnit_mul data)) :=
  cornerLift_stable
    (B0 := sourceEdgeAlgebra data) (B1 := targetEdgeAlgebra data)
    (theta := edgeIsomorphism data)
    (iA := amalgamLeftInclusion data) (iB := amalgamRightInclusion data)
    (e := cornerUnit data) (he_star := cornerUnit_star data)
    (he_mul := cornerUnit_mul data) (pi := cornerBaseMap data)
    (u := cornerStableUnitary data)
    (hcov := cornerStableUnitary_covariance data)
    (hne := cornerUnit_cornerProjectionAt_ne_zero data)

/-- The evaluated corner map composed with the pinned lift is the upper-left
corner of the coordinate evaluation.  Both are lifts of the same covariant
pair to the corner of `M₂(R.carrier)`, which is a same-universe codomain, so
the universal property applies and the two agree. -/
theorem evaluatedCornerMap_comp_uedaCornerLiftPinned (R : HNNCoordinate data) :
    (evaluatedCornerMap data R).comp (uedaCornerLiftPinned data) =
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
      exact (congrArg (evaluatedCornerMap data R)
        (uedaCornerLiftPinned_base data d)).trans
        (evaluatedCornerMap_base data R d)
    · exact (congrArg (evaluatedCornerMap data R)
        (uedaCornerLiftPinned_stable data)).trans
        (evaluatedCornerMap_stable data R)
  · constructor
    · intro d
      simp
    · simp

/-- The pinned lift is injective, by the coordinate argument of the printed
proof. -/
theorem uedaCornerLiftPinned_injective :
    Function.Injective (uedaCornerLiftPinned data) := by
  intro x y hxy
  refine universalCStarHNN_eq_of_forall_eval_eq _ _ _ fun R ↦ ?_
  apply cStarUpperLeftCornerMap_injective
  have hx : cStarUpperLeftCornerMap (universalCStarHNNEval
        (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
        (edgeIsomorphism data) R x) =
      evaluatedCornerMap data R (uedaCornerLiftPinned data x) :=
    (DFunLike.congr_fun
      (evaluatedCornerMap_comp_uedaCornerLiftPinned data R) x).symm
  have hy : cStarUpperLeftCornerMap (universalCStarHNNEval
        (sourceEdgeAlgebra data) (targetEdgeAlgebra data)
        (edgeIsomorphism data) R y) =
      evaluatedCornerMap data R (uedaCornerLiftPinned data y) :=
    (DFunLike.congr_fun
      (evaluatedCornerMap_comp_uedaCornerLiftPinned data R) y).symm
  exact hx.trans ((congrArg (evaluatedCornerMap data R) hxy).trans hy.symm)

/-- **Printed Step 1, closed through the pinned instantiation.**  The same
statement as `uedaCornerMap_proved`, reached without ever solving a
metavariable through the packaged amalgam. -/
theorem uedaCornerMap_concrete : UedaCornerMapStatement := by
  intro G _ S T phi A _ X _ data
  exact ⟨uedaCornerLiftPinned data, uedaCornerLiftPinned_base data,
    uedaCornerLiftPinned_stable data, uedaCornerLiftPinned_injective data⟩

end

end HNNPermanence
end MFRecognition
end Manuscript
end GroupApproximation
