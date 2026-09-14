import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellCellLobeSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Excising a carrier lobe that reads `1`: the arcs, the cell, the exterior and the value

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, across one relator cell `Π`, at walk level: a closed
pocket walk `s ++ invDarts B` with the exterior face off its side, where some rotation of the
carrier of `Π` reads `q B p A`.  Let `invDarts B = l₁ ++ L ++ l₂` with `L` a lobe reading `1`
(`PocketWalkCellLobeExcisionShape`).  Excising `L` leaves the walk `s ++ l₁ ++ l₂`, whose carrier
part consists of two arcs of `Π`.  This module supplies the inputs of the two-arc loop cut
`false_of_pocketRegion_of_below_twoArcs` for that walk, when it is simple.

* `exists_arcs_of_excision`: `l₁ = invDarts A₁` and `l₂ = invDarts A₂` for arcs `A₁`, `A₂` of `Π`.
* `cell_not_mem_sideFaces_excision`: `Π` is off the side of the excised walk, when `l₁ ++ l₂` is
  nonempty, since `Π` is across each of its darts.
* `outerFace_not_mem_sideFaces_excision`: the exterior face is off the side of the excised walk.  An
  edge of the pocket walk off the excised walk lies on `L`, and `Π` is across it, so the face
  classes of the excised walk meet no such edge (`sideFaces_subset_of_agree`).
* `listVal_excision_eq`: the excised walk reads the value of the pocket walk.

## Manuscript status

Infrastructure for `thm:hull` (tex 2121, Hull's small cancellation theorem, through Osin's
Lemma 9.4, Case 1).  It certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open Embedded SimpleClosedWalkSides

namespace SameCellCellLobe

section Excision

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- **The two arcs left by an excision.** -/
theorem exists_arcs_of_excision {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    {l₁ L l₂ : List Delta.toCombMap.Dart} (hsplit : invDarts Delta B = l₁ ++ L ++ l₂) :
    ∃ A₁ A₂ : CyclicArc (cellDarts Delta j),
      l₁ = invDarts Delta A₁.darts ∧ l₂ = invDarts Delta A₂.darts := by
  have hB : B = invDarts Delta l₂ ++ invDarts Delta L ++ invDarts Delta l₁ := by
    rw [← invDarts_invDarts B, hsplit, invDarts_append, invDarts_append]
    simp only [List.append_assoc]
  have hrot₂ : (cellDarts Delta j).rotate (n + targetArc.darts.length) =
      invDarts Delta l₂ ++
        (invDarts Delta L ++ invDarts Delta l₁ ++ sourceArc.darts ++ A ++ targetArc.darts) := by
    have hl : targetArc.darts ++ (invDarts Delta l₂ ++ invDarts Delta L ++ invDarts Delta l₁) ++
          sourceArc.darts ++ A =
        targetArc.darts ++
          (invDarts Delta l₂ ++ invDarts Delta L ++ invDarts Delta l₁ ++ sourceArc.darts ++ A) := by
      simp only [List.append_assoc]
    rw [← List.rotate_rotate, hPi, hB, hl, List.rotate_append_length_eq]
    simp only [List.append_assoc]
  have hrot₁ : (cellDarts Delta j).rotate
        (n + (targetArc.darts ++ invDarts Delta l₂ ++ invDarts Delta L).length) =
      invDarts Delta l₁ ++
        (sourceArc.darts ++ A ++ (targetArc.darts ++ invDarts Delta l₂ ++ invDarts Delta L)) := by
    have hl : targetArc.darts ++ (invDarts Delta l₂ ++ invDarts Delta L ++ invDarts Delta l₁) ++
          sourceArc.darts ++ A =
        (targetArc.darts ++ invDarts Delta l₂ ++ invDarts Delta L) ++
          (invDarts Delta l₁ ++ sourceArc.darts ++ A) := by
      simp only [List.append_assoc]
    rw [← List.rotate_rotate, hPi, hB, hl, List.rotate_append_length_eq]
    simp only [List.append_assoc]
  obtain ⟨A₁, hA₁⟩ := CyclicArc.exists_darts_eq_of_rotate_eq hrot₁
  obtain ⟨A₂, hA₂⟩ := CyclicArc.exists_darts_eq_of_rotate_eq hrot₂
  exact ⟨A₁, A₂, by rw [hA₁, invDarts_invDarts], by rw [hA₂, invDarts_invDarts]⟩

/-- **`Π` is off the side of the excised walk.** -/
theorem cell_not_mem_sideFaces_excision {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    {s l₁ L l₂ : List Delta.toCombMap.Dart} (hsplit : invDarts Delta B = l₁ ++ L ++ l₂)
    (hw : IsSimpleClosedWalk Delta.toCombMap (s ++ l₁ ++ l₂)) (hne : l₁ ++ l₂ ≠ []) :
    (cell Delta j).face ∉ sideFaces Delta.toCombMap (s ++ l₁ ++ l₂) := by
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil (l₁ ++ l₂) hne
  have hdB : Delta.toCombMap.alpha d ∈ B :=
    SameCellPocketSides.alpha_mem_of_mem_invDarts (by
      rw [hsplit]
      rcases List.mem_append.mp hd with h | h
      · exact List.mem_append_left _ (List.mem_append_left _ h)
      · exact List.mem_append_right _ h)
  have hface : Delta.toCombMap.faceOf (Delta.toCombMap.alpha d) = (cell Delta j).face :=
    SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hdB)))
  have hdM : d ∈ s ++ l₁ ++ l₂ := by
    rcases List.mem_append.mp hd with h | h
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h
  rw [← hface]
  exact And.right ((hw.isBoundaryDart_sideFaces_iff Delta.planar d).mpr hdM)

/-- **The exterior face is off the side of the excised walk.** -/
theorem outerFace_not_mem_sideFaces_excision {j : Fin Delta.rCellCount}
    (sourceArc targetArc : CyclicArc (cellDarts Delta j)) {B A : List Delta.toCombMap.Dart} {n : ℕ}
    (hPi : (cellDarts Delta j).rotate n = targetArc.darts ++ B ++ sourceArc.darts ++ A)
    {s l₁ L l₂ : List Delta.toCombMap.Dart} (hsplit : invDarts Delta B = l₁ ++ L ++ l₂)
    (hw : IsSimpleClosedWalk Delta.toCombMap (s ++ l₁ ++ l₂)) (hne : l₁ ++ l₂ ≠ [])
    (hout : Delta.outerFace ∉ sideFaces Delta.toCombMap (s ++ invDarts Delta B)) :
    Delta.outerFace ∉ sideFaces Delta.toCombMap (s ++ l₁ ++ l₂) := by
  have hcell := cell_not_mem_sideFaces_excision sourceArc targetArc hPi hsplit hw hne
  have hsub : ∀ d ∈ s ++ l₁ ++ l₂, d ∈ s ++ invDarts Delta B := by
    intro d hd
    rw [hsplit]
    rcases List.mem_append.mp hd with h | h
    · rcases List.mem_append.mp h with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ h))
    · exact List.mem_append_right _ (List.mem_append_right _ h)
  intro hext
  refine hout (sideFaces_subset_of_agree hsub ?_ hext)
  intro d hd y hdy hkw
  by_contra hkM
  have hdα : Relation.EqvGen (CombMap.FaceClassStep Delta.toCombMap
      (walkKeep Delta.toCombMap (s ++ l₁ ++ l₂))) d (Delta.toCombMap.alpha y) :=
    Relation.EqvGen.trans _ _ _ hdy (Relation.EqvGen.rel _ _ (Or.inr ⟨hkM, rfl⟩))
  have hoff : ∀ z, (z = y ∨ z = Delta.toCombMap.alpha y) → z ∈ s ++ invDarts Delta B →
      z ∉ s ++ l₁ ++ l₂ → False := by
    intro z hz hzw hzM
    have hzα : Relation.EqvGen (CombMap.FaceClassStep Delta.toCombMap
        (walkKeep Delta.toCombMap (s ++ l₁ ++ l₂))) d (Delta.toCombMap.alpha z) := by
      rcases hz with rfl | rfl
      · exact hdα
      · rw [Delta.toCombMap.alpha_involutive y]
        exact hdy
    have hzL : z ∈ L := by
      rw [hsplit] at hzw
      rcases List.mem_append.mp hzw with h | h
      · exact absurd (List.mem_append_left _ (List.mem_append_left _ h)) hzM
      · rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact absurd (List.mem_append_left _ (List.mem_append_right _ h)) hzM
          · exact h
        · exact absurd (List.mem_append_right _ h) hzM
    have hαB : Delta.toCombMap.alpha z ∈ B :=
      SameCellPocketSides.alpha_mem_of_mem_invDarts (by
        rw [hsplit]
        exact List.mem_append_left _ (List.mem_append_right _ hzL))
    have hPiz := SameCellPocketSides.faceOf_of_mem_cellDarts_rotate hPi
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hαB)))
    apply hcell
    rw [← hPiz]
    exact (mem_sideFaces_iff Delta.toCombMap (s ++ l₁ ++ l₂) _).mpr ⟨d, hd, hzα⟩
  unfold walkKeep at hkw hkM
  rcases hkw with h | h
  · exact hoff y (Or.inl rfl) h (fun hyM => hkM (Or.inl hyM))
  · exact hoff (Delta.toCombMap.alpha y) (Or.inr rfl) h (fun hyM => hkM (Or.inr hyM))

/-- **The excised walk reads the value of the pocket walk.** -/
theorem listVal_excision_eq {s l₁ L l₂ : List Delta.toCombMap.Dart}
    (hL : RelLetter.listVal (dartWord Delta L) = 1) :
    RelLetter.listVal (dartWord Delta (s ++ l₁ ++ l₂)) =
      RelLetter.listVal (dartWord Delta (s ++ (l₁ ++ L ++ l₂))) := by
  have happ : ∀ a b : List Delta.toCombMap.Dart,
      RelLetter.listVal (dartWord Delta (a ++ b)) =
        RelLetter.listVal (dartWord Delta a) * RelLetter.listVal (dartWord Delta b) := by
    intro a b
    simp [Embedded.dartWord, RelLetter.listVal]
  simp only [happ, hL, mul_one, mul_assoc]

end Excision

end SameCellCellLobe

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.exists_arcs_of_excision
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.cell_not_mem_sideFaces_excision
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.outerFace_not_mem_sideFaces_excision
#audit_axioms GroupApproximation.GGT.VanKampen.SameCellCellLobe.listVal_excision_eq
