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
open GroupApproximation.GGT.DGOPolygonCut

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
  calc
    (vertex A.basepoint A.word (A.cut s))⁻¹ *
        vertex A.basepoint A.word (A.cut (s + 1)) =
      (vertex A.basepoint A.word (A.cut s))⁻¹ *
        vertex A.basepoint A.word (A.cut s + 1) := by
          exact congrArg
            (fun t => (vertex A.basepoint A.word (A.cut s))⁻¹ *
              vertex A.basepoint A.word t) (A.target_edge s hs)
    _ = (A.word[A.cut s]'hlt).val := by
      rw [vertex_succ A.word A.basepoint (A.cut s) hlt]
      group

end AuxiliaryCycleCertificate

namespace AuxiliaryCyclePathInput

/-- A nonempty one-letter right connector has side span equal to the value of
the whole connector word. -/
theorem rightConnector_sideSpan
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} (Q : AuxiliaryCyclePathInput D hsymm b)
    (hpos : 0 < Q.right.length) (hone : Q.right.length ≤ 1) :
    Q.certificate.sideSpan (Q.left.length + Q.arcSides) =
      RelLetter.listVal Q.right := by
  have ht : Q.left.length + Q.arcSides ∈ Q.certificate.target := by
    change Q.left.length + Q.arcSides ∈ Q.localTarget ∪
      DGOPolygonCut.auxiliaryCycleConnectorTarget
        Q.left Q.right Q.arcSides
    exact Finset.mem_union.mpr (Or.inr
      (DGOPolygonCut.mem_auxiliaryCycleConnectorTarget_right
        Q.left Q.right Q.arcSides 0 hpos))
  have hspan := Q.certificate.sideSpan_eq_targetLetter ht
  have hcut := auxiliaryCycleCut_right Q.left Q.right
    Q.arcPolygon.cut (r := 0) (by omega)
  change Q.certificate.sideSpan (Q.left.length + Q.arcSides) =
    ((auxiliaryCycleWord Q.left Q.arc Q.right Q.chord)[
      auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right
        (Q.left.length + Q.arcSides)]'_).val at hspan
  rw [hcut] at hspan
  rcases hright : Q.right with _ | ⟨a, t⟩
  · simp at hpos
  · have ht : t = [] := by
      apply List.length_eq_zero_iff.mp
      have hlen := hone
      simp only [hright, List.length_cons] at hlen
      omega
    subst t
    simpa [hright, auxiliaryCycleWord, OsinComponents.length_revWord,
      listVal_singleton, RelLetter.val] using hspan

/-- A nonempty one-letter left connector is read backwards at the beginning
of the auxiliary cycle, so its side span is the inverse connector value. -/
theorem leftConnector_sideSpan
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} (Q : AuxiliaryCyclePathInput D hsymm b)
    (hpos : 0 < Q.left.length) (hone : Q.left.length ≤ 1) :
    Q.certificate.sideSpan 0 = (RelLetter.listVal Q.left)⁻¹ := by
  have ht : 0 ∈ Q.certificate.target := by
    change 0 ∈ Q.localTarget ∪
      DGOPolygonCut.auxiliaryCycleConnectorTarget
        Q.left Q.right Q.arcSides
    exact Finset.mem_union.mpr (Or.inr
      (DGOPolygonCut.mem_auxiliaryCycleConnectorTarget_left
        Q.left Q.right Q.arcSides 0 hpos))
  have hspan := Q.certificate.sideSpan_eq_targetLetter ht
  have hcut := auxiliaryCycleCut_left Q.left Q.right Q.arcSides Q.arcCut
    (r := 0) (by omega)
  change Q.certificate.sideSpan 0 =
    ((auxiliaryCycleWord Q.left Q.arc Q.right Q.chord)[
      auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right 0]'_).val at hspan
  rw [hcut] at hspan
  rcases hleft : Q.left with _ | ⟨a, t⟩
  · simp at hpos
  · have ht : t = [] := by
      apply List.length_eq_zero_iff.mp
      have hlen := hone
      simp only [hleft, List.length_cons] at hlen
      omega
    subst t
    simpa [hleft, auxiliaryCycleWord, revWord, invLetter,
      listVal_singleton, RelLetter.val] using hspan

end AuxiliaryCyclePathInput

namespace TwoHalfTargetSlot

/-- A slot tagged by a first child has the value of that child's target
letter. -/
theorem span_eq_firstTargetLetter
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : DGOPolygonCut.TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
    (X : TwoHalfTargetSlot A lam)
    (j : Fin index.first.pieceCount) (hchild : X.child = Sum.inl j) :
    twoHalfChildSpan A X.child X.targetIndex =
      ((A.firstChildren j).word[(A.firstChildren j).cut X.targetIndex]'
        (by
          have ht : X.targetIndex ∈ (A.firstChildren j).target := by
            simpa [twoHalfChildTarget, hchild] using X.target_mem
          have hc := (A.firstChildren j).target_component X.targetIndex ht
          exact hc.1.trans_le hc.2.1)).val := by
  have ht : X.targetIndex ∈ (A.firstChildren j).target := by
    simpa [twoHalfChildTarget, hchild] using X.target_mem
  simpa [twoHalfChildSpan, hchild] using
    (A.firstChildren j).sideSpan_eq_targetLetter ht

/-- A slot tagged by a second child has the value of that child's target
letter. -/
theorem span_eq_secondTargetLetter
    {D : RelGenSet G Λ} {b : ℝ}
    {I₁ I₂ : Finset ℕ} {pos₁ partner₁ pos₂ partner₂ : ℕ → ℕ}
    {chordLength : ℕ}
    {index : DGOPolygonCut.TwoHalfGreedyFamilyIndex I₁ I₂
      pos₁ partner₁ pos₂ partner₂ chordLength}
    {A : TwoHalfAuxiliaryCycleFamily D b index} {lam : Λ}
    (X : TwoHalfTargetSlot A lam)
    (j : Fin index.second.pieceCount) (hchild : X.child = Sum.inr j) :
    twoHalfChildSpan A X.child X.targetIndex =
      ((A.secondChildren j).word[(A.secondChildren j).cut X.targetIndex]'
        (by
          have ht : X.targetIndex ∈ (A.secondChildren j).target := by
            simpa [twoHalfChildTarget, hchild] using X.target_mem
          have hc := (A.secondChildren j).target_component X.targetIndex ht
          exact hc.1.trans_le hc.2.1)).val := by
  have ht : X.targetIndex ∈ (A.secondChildren j).target := by
    simpa [twoHalfChildTarget, hchild] using X.target_mem
  simpa [twoHalfChildSpan, hchild] using
    (A.secondChildren j).sideSpan_eq_targetLetter ht

end TwoHalfTargetSlot

end DGOProposition414
end GGT
end GroupApproximation
