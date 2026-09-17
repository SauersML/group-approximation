import GroupApproximation.Analysis.KasparovUnitaryEquivalence
import GroupApproximation.Meta.AxiomGuard

/-!
# Kasparov operators on a fixed frame

A Kasparov bimodule `(E, γ, π, F)` has two kinds of data.  The *frame* is the graded Hilbert
module with its representation, `(E, γ, π)`.  The *operator* is `F`.  An operator homotopy
moves the operator and keeps the frame fixed.  So the five clauses that involve `F` are split
off here into a predicate on the frame:

* `IsKasparovOp E γ ρ F`: `F` is bounded and odd, and `(F² - 1)ρ(a)`, `(F - F⋆)ρ(a)` and
  `[F, ρ(a)]` are compact.

## The proof route

* `isKasparovOp_op`: the operator of a bimodule is a Kasparov operator on its frame.
* `IsKasparovOp.congr`: the predicate depends only on `F.toFun`.  The adjoint of `F` is fixed by
  `F.toFun` (`Adjointable.adj_eq_of_toFun_eq`), and `IsCompactOp` is pointwise
  (`Adjointable.IsCompactOp.congr`).
* `IsKasparovOp.prodMap`: the direct sum of two Kasparov operators is one.  The proof copies
  `KasparovBimodule.add`.
* `withOp M F hF`: the bimodule with the frame of `M` and the operator `F`.  `withOp_self`
  (`withOp M M.op _ = M`) holds by structure eta.

The predicate takes the frame, not a bimodule.  So the frame of `withOp M F hF` is
definitionally the frame of `M`, and a predicate about `withOp M F hF` can be read as one about
`M`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KKMonoidLane

open HilbertModule

universe u v w w'

/-- **`F` is a Kasparov operator on the frame `(E, γ, ρ)`**: bounded, odd, a selfadjoint
involution modulo compacts after multiplying by `ρ(a)`, and commuting with `ρ` modulo compacts.
These are the five clauses of `KasparovBimodule` that involve the operator. -/
structure IsKasparovOp {A : Type u} [NonUnitalCStarAlgebra A] {B : Type v}
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (E : CStarModule.{v, w} B) (γ : Adjointable E E) (ρ : A → Adjointable E E)
    (F : Adjointable E E) : Prop where
  /-- `F` is bounded. -/
  bounded : F.IsBounded
  /-- `F` is odd. -/
  odd : ∀ x : E.carrier, γ.toFun (F.toFun x) = -(F.toFun (γ.toFun x))
  /-- `(F² - 1)ρ(a)` is compact. -/
  compact_one : ∀ a : A,
    (((F.comp F).sub (Adjointable.id E)).comp (ρ a)).IsCompactOp
  /-- `(F - F⋆)ρ(a)` is compact. -/
  compact_selfAdjoint : ∀ a : A,
    ((F.sub (Adjointable.adjoint F)).comp (ρ a)).IsCompactOp
  /-- `[F, ρ(a)]` is compact. -/
  compact_commutator : ∀ a : A,
    ((F.comp (ρ a)).sub ((ρ a).comp F)).IsCompactOp

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.IsKasparovOp

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The operator of a Kasparov bimodule is a Kasparov operator on its frame. -/
theorem isKasparovOp_op (M : KasparovBimodule.{u, v, w} A B) :
    IsKasparovOp M.E M.grading M.pi M.op :=
  ⟨M.op_bounded, M.op_odd, M.compact_one, M.compact_selfAdjoint, M.compact_commutator⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.isKasparovOp_op

/-- Being a Kasparov operator depends only on the underlying map. -/
theorem IsKasparovOp.congr {E : CStarModule.{v, w} B} {γ : Adjointable E E}
    {ρ : A → Adjointable E E} {F G : Adjointable E E} (hF : IsKasparovOp E γ ρ F)
    (h : ∀ x, F.toFun x = G.toFun x) : IsKasparovOp E γ ρ G where
  bounded := hF.bounded.congr h
  odd x := by
    rw [← h x, ← h (γ.toFun x)]
    exact hF.odd x
  compact_one a := Adjointable.IsCompactOp.congr (fun x => by
      show F.toFun (F.toFun ((ρ a).toFun x)) - (ρ a).toFun x
        = G.toFun (G.toFun ((ρ a).toFun x)) - (ρ a).toFun x
      rw [h, h]) (hF.compact_one a)
  compact_selfAdjoint a := Adjointable.IsCompactOp.congr (fun x => by
      show F.toFun ((ρ a).toFun x) - F.adj ((ρ a).toFun x)
        = G.toFun ((ρ a).toFun x) - G.adj ((ρ a).toFun x)
      rw [h, Adjointable.adj_eq_of_toFun_eq F G h]) (hF.compact_selfAdjoint a)
  compact_commutator a := Adjointable.IsCompactOp.congr (fun x => by
      show F.toFun ((ρ a).toFun x) - (ρ a).toFun (F.toFun x)
        = G.toFun ((ρ a).toFun x) - (ρ a).toFun (G.toFun x)
      rw [h ((ρ a).toFun x), h x]) (hF.compact_commutator a)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.IsKasparovOp.congr

/-- The direct sum of two Kasparov operators is a Kasparov operator on the direct-sum frame. -/
theorem IsKasparovOp.prodMap {E : CStarModule.{v, w} B} {E' : CStarModule.{v, w'} B}
    {γ F : Adjointable E E} {ρ : A → Adjointable E E}
    {γ' G : Adjointable E' E'} {ρ' : A → Adjointable E' E'}
    (hF : IsKasparovOp E γ ρ F) (hG : IsKasparovOp E' γ' ρ' G) :
    IsKasparovOp (prod E E') (Adjointable.prodMap γ γ')
      (fun a => Adjointable.prodMap (ρ a) (ρ' a)) (Adjointable.prodMap F G) where
  bounded := Adjointable.IsBounded.prodMap hF.bounded hG.bounded
  odd p := Prod.ext (hF.odd p.1) (hG.odd p.2)
  compact_one a :=
    Adjointable.IsCompactOp.congr (fun _ => rfl)
      (Adjointable.IsCompactOp.prodMap (hF.compact_one a) (hG.compact_one a))
  compact_selfAdjoint a :=
    Adjointable.IsCompactOp.congr (fun _ => rfl)
      (Adjointable.IsCompactOp.prodMap (hF.compact_selfAdjoint a)
        (hG.compact_selfAdjoint a))
  compact_commutator a :=
    Adjointable.IsCompactOp.congr (fun _ => rfl)
      (Adjointable.IsCompactOp.prodMap (hF.compact_commutator a)
        (hG.compact_commutator a))

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.IsKasparovOp.prodMap

/-- **The bimodule `M` with its operator replaced by `F`.**  The frame is the frame of `M`. -/
def withOp (M : KasparovBimodule.{u, v, w} A B) (F : Adjointable M.E M.E)
    (hF : IsKasparovOp M.E M.grading M.pi F) : KasparovBimodule.{u, v, w} A B where
  E := M.E
  grading := M.grading
  pi := M.pi
  op := F
  grading_bounded := M.grading_bounded
  grading_selfAdjoint := M.grading_selfAdjoint
  grading_involutive := M.grading_involutive
  rep := M.rep
  rep_even := M.rep_even
  op_bounded := hF.bounded
  op_odd := hF.odd
  compact_one := hF.compact_one
  compact_selfAdjoint := hF.compact_selfAdjoint
  compact_commutator := hF.compact_commutator

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.withOp

/-- Replacing the operator by itself changes nothing. -/
theorem withOp_self (M : KasparovBimodule.{u, v, w} A B) :
    withOp M M.op (isKasparovOp_op M) = M :=
  rfl

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.withOp_self

end KKMonoidLane
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
