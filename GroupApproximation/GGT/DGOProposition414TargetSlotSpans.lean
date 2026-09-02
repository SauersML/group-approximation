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

/-- A side on the final chord block has the span of the corresponding chord
letter. -/
theorem chord_sideSpan_eq_letter
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} (Q : AuxiliaryCyclePathInput D hsymm b)
    (r : ℕ) (hr : r < Q.chord.length) :
    Q.certificate.sideSpan
      (Q.left.length + Q.arcSides + Q.right.length + r) =
        (Q.chord[r]'hr).val := by
  let word := auxiliaryCycleWord Q.left Q.arc Q.right Q.chord
  let off := Q.left.length + Q.arc.length + Q.right.length
  let t := Q.left.length + Q.arcSides + Q.right.length + r
  have hcut0 := auxiliaryCycleCut_chord Q.left Q.right Q.arcPolygon.cut
    (r := r)
  have hcut1 := auxiliaryCycleCut_chord Q.left Q.right Q.arcPolygon.cut
    (r := r + 1)
  have hcut1' : auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right
      (t + 1) = off + (r + 1) := by
    have ht : t + 1 =
        Q.left.length + Q.arcSides + Q.right.length + (r + 1) := by
      dsimp [t]
      omega
    rw [ht, hcut1]
  change (vertex Q.basepoint word
      (auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right t))⁻¹ *
      vertex Q.basepoint word
        (auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right (t + 1)) =
      (Q.chord[r]'hr).val
  calc
    _ = (vertex Q.basepoint word (off + r))⁻¹ *
        vertex Q.basepoint word (off + (r + 1)) := by
          exact congrArg₂ (fun x y : G => x⁻¹ * y)
            (congrArg (vertex Q.basepoint word) (by
              dsimp [t, off]
              exact hcut0))
            (congrArg (vertex Q.basepoint word) hcut1')
    _ = (vertex
          (Q.basepoint * RelLetter.listVal
            ((revWord Q.left ++ Q.arc) ++ Q.right)) Q.chord r)⁻¹ *
        vertex
          (Q.basepoint * RelLetter.listVal
            ((revWord Q.left ++ Q.arc) ++ Q.right)) Q.chord (r + 1) := by
          rw [show off + r = Q.left.length + Q.arc.length +
              Q.right.length + r by rfl,
            show off + (r + 1) = Q.left.length + Q.arc.length +
              Q.right.length + (r + 1) by rfl,
            vertex_auxiliaryCycle_chord, vertex_auxiliaryCycle_chord]
    _ = (Q.chord[r]'hr).val := by
      rw [vertex_succ Q.chord
        (Q.basepoint * RelLetter.listVal
          ((revWord Q.left ++ Q.arc) ++ Q.right)) r hr]
      group

/-- The local edge of an oriented segment is the forward chord edge when the
segment runs forward and its inverse when it runs backwards. -/
theorem orientedEdgeIndex_val
    (word : List (RelLetter G Λ)) {a b y : ℕ}
    (ha : a ≤ word.length) (hb : b ≤ word.length)
    (hy : y < word.length) (hedge : EdgeBetween a b y) :
    ((orientedSegment word a b)[orientedEdgeIndex a b y]'
      (orientedEdgeIndex_lt word ha hb hedge)).val =
      if a ≤ b then (word[y]'hy).val else (word[y]'hy).val⁻¹ := by
  have hor := hedge
  unfold EdgeBetween at hor
  by_cases hab : a ≤ b
  · have hforward : a ≤ y ∧ y + 1 ≤ b := by omega
    simp only [orientedSegment, if_pos hab, orientedEdgeIndex]
    simp only [List.getElem_take, List.getElem_drop,
      Nat.add_sub_of_le hforward.1]
  · have hba : b ≤ a := by omega
    have hreverse : b ≤ y ∧ y + 1 ≤ a := by omega
    let segment := (word.drop b).take (a - b)
    have hsegmentLen : segment.length = a - b := by
      dsimp [segment]
      rw [List.length_take, List.length_drop]
      omega
    have hlocal : a - (y + 1) < segment.length := by
      rw [hsegmentLen]
      omega
    have hforwardIndex : y - b < segment.length := by
      rw [hsegmentLen]
      omega
    have hsegmentLetter : segment[y - b]'hforwardIndex = word[y]'hy := by
      dsimp [segment]
      simp only [List.getElem_take, List.getElem_drop,
        Nat.add_sub_of_le hreverse.1]
    have hindex : segment.length - 1 - (a - (y + 1)) = y - b := by
      rw [hsegmentLen]
      omega
    have hrev := getElem_revWord segment
      (m := a - (y + 1)) (by
        rw [OsinComponents.length_revWord]
        exact hlocal) (by rw [hindex]; exact hforwardIndex)
    rw [getElem_congr_idx hindex, hsegmentLetter] at hrev
    simp only [orientedSegment, if_neg hab, orientedEdgeIndex]
    rw [hrev, val_invLetter]

/-- A nonempty one-letter right connector has side span equal to the value of
the whole connector word. -/
theorem rightConnector_sideSpan
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} (Q : AuxiliaryCyclePathInput D hsymm b)
    (hpos : 0 < Q.right.length) (hone : Q.right.length ≤ 1) :
    Q.certificate.sideSpan (Q.left.length + Q.arcSides) =
      RelLetter.listVal Q.right := by
  have hlen : Q.right.length = 1 := by omega
  have hcut0 := auxiliaryCycleCut_right Q.left Q.right
    Q.arcPolygon.cut (r := 0) (by omega)
  have hcut1 := auxiliaryCycleCut_right Q.left Q.right
    Q.arcPolygon.cut (r := 1) (by omega)
  have hcut1' : auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right
      (Q.left.length + Q.arcSides + 1) =
      Q.left.length + Q.arc.length + 1 := by
    simpa only [Nat.add_zero] using hcut1
  let word := auxiliaryCycleWord Q.left Q.arc Q.right Q.chord
  let off := Q.left.length + Q.arc.length
  have hoff : off < word.length := by
    dsimp [off, word]
    simp [auxiliaryCycleWord, OsinComponents.length_revWord]
    omega
  change (vertex Q.basepoint word
      (auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right
        (Q.left.length + Q.arcSides)))⁻¹ *
      vertex Q.basepoint word
        (auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right
          (Q.left.length + Q.arcSides + 1)) = RelLetter.listVal Q.right
  calc
    _ = (vertex Q.basepoint word off)⁻¹ *
        vertex Q.basepoint word (off + 1) := by
          exact congrArg₂ (fun x y : G => x⁻¹ * y)
            (congrArg (vertex Q.basepoint word) (by
              simpa only [Nat.add_zero, off] using hcut0))
            (congrArg (vertex Q.basepoint word) (by
              simpa only [off] using hcut1'))
    _ = (word[off]'hoff).val := by
      rw [vertex_succ word Q.basepoint off hoff]
      group
    _ = RelLetter.listVal Q.right := by
      let a := Q.right[0]'hpos
      have hright : Q.right = [a] := by
        apply List.ext_getElem
        · simp [hlen]
        · intro i hi hi'
          have hi0 : i = 0 := by
            simp only [List.length_singleton] at hi'
            omega
          subst i
          rfl
      have hletter :
          (word[off]'hoff) = a := by
        dsimp [word, off, a]
        unfold auxiliaryCycleWord
        rw [List.getElem_append_left (by
          simp [OsinComponents.length_revWord]
          omega)]
        rw [List.getElem_append_right (by
          simp [OsinComponents.length_revWord])]
        simp [OsinComponents.length_revWord]
      rw [hletter, hright, listVal_singleton]

/-- A nonempty one-letter left connector is read backwards at the beginning
of the auxiliary cycle, so its side span is the inverse connector value. -/
theorem leftConnector_sideSpan
    {D : RelGenSet G Λ} {hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base}
    {b : ℕ} (Q : AuxiliaryCyclePathInput D hsymm b)
    (hpos : 0 < Q.left.length) (hone : Q.left.length ≤ 1) :
    Q.certificate.sideSpan 0 = (RelLetter.listVal Q.left)⁻¹ := by
  have hlen : Q.left.length = 1 := by omega
  have hcut0 := auxiliaryCycleCut_left Q.left Q.right Q.arcSides Q.arcCut
    (r := 0) (by omega)
  have hcut1 := auxiliaryCycleCut_left Q.left Q.right Q.arcSides Q.arcCut
    (r := 1) (by omega)
  let word := auxiliaryCycleWord Q.left Q.arc Q.right Q.chord
  have hzero : 0 < word.length := by
    dsimp [word]
    simp [auxiliaryCycleWord, OsinComponents.length_revWord]
    omega
  change (vertex Q.basepoint word
      (auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right 0))⁻¹ *
      vertex Q.basepoint word
        (auxiliaryCycleCut Q.left Q.arcSides Q.arcCut Q.right 1) =
      (RelLetter.listVal Q.left)⁻¹
  calc
    _ = (vertex Q.basepoint word 0)⁻¹ *
        vertex Q.basepoint word 1 := by
          exact congrArg₂ (fun x y : G => x⁻¹ * y)
            (congrArg (vertex Q.basepoint word) hcut0)
            (congrArg (vertex Q.basepoint word) hcut1)
    _ = (word[0]'hzero).val := by
      rw [vertex_succ word Q.basepoint 0 hzero]
      group
    _ = (RelLetter.listVal Q.left)⁻¹ := by
      let a := Q.left[0]'hpos
      have hleft : Q.left = [a] := by
        apply List.ext_getElem
        · simp [hlen]
        · intro i hi hi'
          have hi0 : i = 0 := by
            simp only [List.length_singleton] at hi'
            omega
          subst i
          rfl
      have hrev : (revWord Q.left)[0]'(by
          rw [OsinComponents.length_revWord]
          exact hpos) = invLetter a := by
        have h := getElem_revWord Q.left (m := 0) (by
          rw [OsinComponents.length_revWord]
          exact hpos) (by omega)
        simpa [a, hlen] using h
      have hletter : (word[0]'hzero) = invLetter a := by
        dsimp [word]
        unfold auxiliaryCycleWord
        rw [List.getElem_append_left (by
          simp [OsinComponents.length_revWord]
          omega),
          List.getElem_append_left (by
            simp [OsinComponents.length_revWord]
            omega),
          List.getElem_append_left (by
            simp [OsinComponents.length_revWord]
            omega)]
        exact hrev
      rw [hletter, hleft, listVal_singleton, val_invLetter]

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
