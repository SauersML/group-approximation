import GroupApproximation.GGT.DGOProposition414GapConnectorSlots

/-!
# Spans of concrete child target slots

A distinguished side of an auxiliary child is a single edge.  Its stored
`sideSpan` is thus exactly the value of the corresponding auxiliary-cycle
letter.  This elementary identity is the common starting point for the arc,
connector, and chord factor computations in the bisection step of
Dahmani--Guirardel--Osin Proposition 4.14.
-/

namespace GroupApproximation
namespace GGT
namespace DGOProposition414

open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

namespace AuxiliaryCycleCertificate

/-- A target side span is the value of its unique cycle letter. -/
theorem sideSpan_eq_targetLetter
    {D : RelGenSet G Λ} {b : ℝ} {m s : ℕ}
    (A : AuxiliaryCycleCertificate D b m) (hs : s ∈ A.target) :
    A.sideSpan s =
      (A.word[A.cut s]'(by
        have hcomp := A.target_component s hs
        exact hcomp.1.trans_le hcomp.2.1)).val := by
  have hcomp := A.target_component s hs
  have hlt : A.cut s < A.word.length := hcomp.1.trans_le hcomp.2.1
  unfold sideSpan
  rw [A.target_edge s hs, vertex_succ A.word A.basepoint (A.cut s) hlt]
  group

end AuxiliaryCycleCertificate

namespace TwoHalfTargetSlot

/-- A tagged slot span is the target letter of its actual first or second
child. -/
theorem span_eq_targetLetter
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : DGOPolygonCut.TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
    (X : TwoHalfTargetSlot A lam) :
    twoHalfChildSpan A X.child X.targetIndex =
      match h : X.child with
      | Sum.inl j =>
          ((A.firstChildren j).word[(A.firstChildren j).cut X.targetIndex]'
            (by
              have ht : X.targetIndex ∈ (A.firstChildren j).target := by
                simpa [twoHalfChildTarget, h] using X.target_mem
              have hc := (A.firstChildren j).target_component X.targetIndex ht
              exact hc.1.trans_le hc.2.1)).val
      | Sum.inr j =>
          ((A.secondChildren j).word[(A.secondChildren j).cut X.targetIndex]'
            (by
              have ht : X.targetIndex ∈ (A.secondChildren j).target := by
                simpa [twoHalfChildTarget, h] using X.target_mem
              have hc := (A.secondChildren j).target_component X.targetIndex ht
              exact hc.1.trans_le hc.2.1)).val := by
  generalize hchild : X.child = q
  cases q with
  | inl j =>
      have ht : X.targetIndex ∈ (A.firstChildren j).target := by
        simpa [twoHalfChildTarget, hchild] using X.target_mem
      simpa [twoHalfChildSpan, hchild] using
        (A.firstChildren j).sideSpan_eq_targetLetter ht
  | inr j =>
      have ht : X.targetIndex ∈ (A.secondChildren j).target := by
        simpa [twoHalfChildTarget, hchild] using X.target_mem
      simpa [twoHalfChildSpan, hchild] using
        (A.secondChildren j).sideSpan_eq_targetLetter ht

end TwoHalfTargetSlot

end DGOProposition414
end GGT
end GroupApproximation
