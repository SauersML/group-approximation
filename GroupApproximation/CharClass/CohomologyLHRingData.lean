import GroupApproximation.CharClass.CohomologyLHRingSurj

/-!
# `LerayHirschData` from `LerayHirschGraded`

The endpoint of the bridge.  `cc-steenrod` found that nothing in the tree
constructs a `LerayHirschData`, whose freeness field is ring-level, while what the
geometry produces is `LerayHirschGraded`, which is degreewise.  This closes that
gap in one application of each half.

Nothing here is new mathematics.  The degree bookkeeping is `component_lhFun`, the
two halves are `lhFun_injective` and `lhFun_surjective`, and this only assembles
them into the structure `ChernRelation` consumes.

## Main declarations

* `LHCast.lerayHirschData_of_graded` — **the constructor**.
-/

open CategoryTheory

namespace GroupApproximation.CharClass

noncomputable section

namespace LHCast

open LH

variable {X P : TopCat.{0}}

/-- **Leray–Hirsch data from the degreewise statement.**  The projection, the rank
and the class are carried across unchanged; the freeness field is the ring-level
bijectivity, which is the two halves of the bridge. -/
def lerayHirschData_of_graded {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : LerayHirschData X P where
  proj := π
  rank := r
  taut := ξ
  free := ⟨lhFun_injective L, lhFun_surjective L⟩

@[simp] theorem lerayHirschData_of_graded_proj {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : (lerayHirschData_of_graded L).proj = π := rfl

@[simp] theorem lerayHirschData_of_graded_rank {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : (lerayHirschData_of_graded L).rank = r := rfl

@[simp] theorem lerayHirschData_of_graded_taut {π : P ⟶ X} {ξ : Hmod2 P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : (lerayHirschData_of_graded L).taut = ξ := rfl

end LHCast

end

end GroupApproximation.CharClass
