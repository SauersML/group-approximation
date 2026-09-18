import GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoid.OperatorPathTrans
import GroupApproximation.Meta.AxiomGuard

/-!
# Operator homotopy of Kasparov bimodules

`OperatorHomotopic M N` says that `N` has the frame of `M`, and its operator is joined to `M.op`
by a norm-continuous path of Kasparov operators on that frame.  Formally, `N = withOp M F hF`
for some `F` with `OpPath M.E M.grading M.pi M.op F`.

On paper, an odd compact perturbation `F ↦ F + K` is a special case, through the straight path
`F + tK`.  That instance is not formalized in this lane.  Unitary equivalence is a separate
generator of the KK relation (`KKRelation`).

## The proof route

* reflexivity: the constant path, and `withOp_self` (`rfl`);
* symmetry: the reversed path.  `withOp (withOp M F hF) M.op _ = M` holds by structure eta;
* transitivity: the concatenated path (`OpPath.trans`), and
  `withOp (withOp M F hF) G _ = withOp M G _` holds by `rfl`;
* compatibility with `⊞ N`: `s ↦ P s ⊞ N.op` (`OpPath.prodMap_right`), and
  `(withOp M F hF) ⊞ N = withOp (M ⊞ N) (F ⊞ N.op) _` holds by `rfl`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace KKMonoidLane

open HilbertModule

universe u v w

variable {A : Type u} [NonUnitalCStarAlgebra A]
variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- **Operator homotopy**: `N` is `M` with its operator moved along a norm-continuous path of
Kasparov operators on the frame of `M`. -/
def OperatorHomotopic (M N : KasparovBimodule.{u, v, w} A B) : Prop :=
  ∃ (F : Adjointable M.E M.E) (hF : IsKasparovOp M.E M.grading M.pi F),
    OpPath M.E M.grading M.pi M.op F ∧ N = withOp M F hF

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OperatorHomotopic

theorem OperatorHomotopic.refl (M : KasparovBimodule.{u, v, w} A B) : OperatorHomotopic M M :=
  ⟨M.op, isKasparovOp_op M, OpPath.refl (isKasparovOp_op M), rfl⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OperatorHomotopic.refl

theorem OperatorHomotopic.symm {M N : KasparovBimodule.{u, v, w} A B}
    (h : OperatorHomotopic M N) : OperatorHomotopic N M := by
  obtain ⟨F, hF, hp, rfl⟩ := h
  have hM : IsKasparovOp (withOp M F hF).E (withOp M F hF).grading (withOp M F hF).pi M.op :=
    isKasparovOp_op M
  have hq : OpPath (withOp M F hF).E (withOp M F hF).grading (withOp M F hF).pi
      (withOp M F hF).op M.op :=
    hp.symm
  exact ⟨M.op, hM, hq, rfl⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OperatorHomotopic.symm

theorem OperatorHomotopic.trans {M N P : KasparovBimodule.{u, v, w} A B}
    (h₁ : OperatorHomotopic M N) (h₂ : OperatorHomotopic N P) : OperatorHomotopic M P := by
  obtain ⟨F, hF, hp, rfl⟩ := h₁
  obtain ⟨G, hG, hq, rfl⟩ := h₂
  have hG' : IsKasparovOp M.E M.grading M.pi G := hG
  have hq' : OpPath M.E M.grading M.pi F G := hq
  exact ⟨G, hG', hp.trans hq', rfl⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.OperatorHomotopic.trans

/-- **Operator homotopy is an equivalence relation.** -/
theorem operatorHomotopic_equivalence :
    Equivalence (fun M N : KasparovBimodule.{u, v, w} A B => OperatorHomotopic M N) :=
  ⟨OperatorHomotopic.refl, OperatorHomotopic.symm, OperatorHomotopic.trans⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.operatorHomotopic_equivalence

/-- Operator homotopy is compatible with adding a fixed bimodule on the right. -/
theorem operatorHomotopic_add_right {M M' : KasparovBimodule.{u, v, w} A B}
    (h : OperatorHomotopic M M') (N : KasparovBimodule.{u, v, w} A B) :
    OperatorHomotopic (M.add N) (M'.add N) := by
  obtain ⟨F, hF, hp, rfl⟩ := h
  have hK : IsKasparovOp (M.add N).E (M.add N).grading (M.add N).pi
      (Adjointable.prodMap F N.op) :=
    hF.prodMap (isKasparovOp_op N)
  have hq : OpPath (M.add N).E (M.add N).grading (M.add N).pi (M.add N).op
      (Adjointable.prodMap F N.op) :=
    hp.prodMap_right (isKasparovOp_op N)
  exact ⟨Adjointable.prodMap F N.op, hK, hq, rfl⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.KKMonoidLane.operatorHomotopic_add_right

end KKMonoidLane
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
