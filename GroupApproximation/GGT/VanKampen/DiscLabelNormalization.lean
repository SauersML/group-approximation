import GroupApproximation.GGT.VanKampen.GEdgeLabelRepair
import GroupApproximation.GGT.VanKampen.NonemptyConnectorWord
import GroupApproximation.GGT.OsinGeodesicWord

/-!
# Normalizing the labels of an actual relative disc diagram

For a symmetric base alphabet, admissible exterior and relator words allow
every remaining illegal edge to be replaced inside G-faces. Strong induction
on the finite number of illegal darts terminates even when a replacement
lengthens the diagram. The actual subdivision retains the exterior word,
all face traversals, and the complete ordered relator-cell data.
-/

namespace GroupApproximation.GGT.VanKampen.DiscLabelNormalization

open HullSC
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

structure Output (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W) where
  diagram : DiscDiagram.{u, w, v} W
  expansion : DiscExpansion Delta diagram
  cells : Surgery.OrderedRCellMap Delta diagram expansion.faceEquiv
  label_admissible : ∀ d, D.IsLetter (diagram.label d)

theorem outer_admissible (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (Delta : DiscDiagram.{u, w, v} W)
    (hboundary : RelWord.IsAdmissible D Delta.boundaryWord) :
    RelWord.IsAdmissible D (Delta.faceWord Delta.outerFace) := by
  have h := isAdmissible_revInv hsymm hboundary
  simpa only [DiscDiagram.boundaryWord, RelWord.revInv_revInv] using h

theorem illegal_faces (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (Delta : DiscDiagram.{u, w, v} W)
    (hboundary : RelWord.IsAdmissible D Delta.boundaryWord)
    (hcells : ∀ C ∈ Delta.relatorCells, RelWord.IsAdmissible D C.word)
    (a : Delta.toCombMap.Dart) (ha : ¬ D.IsLetter (Delta.label a)) :
    (Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace) ∧
    (∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face) := by
  have hreverse : ¬ D.IsLetter (Delta.label (Delta.toCombMap.alpha a)) := by
    intro hadm
    have h := isLetter_relWordInv D hsymm hadm
    rw [Delta.label_alpha, RelWord.inv_inv_letter] at h
    exact ha h
  have hface (d : Delta.toCombMap.Dart) (hd : ¬ D.IsLetter (Delta.label d))
      (f : Delta.toCombMap.Face) (hf : RelWord.IsAdmissible D (Delta.faceWord f)) :
      Delta.toCombMap.faceOf d ≠ f := by
    intro heq
    exact hd (hf _ (List.mem_map.mpr ⟨d, ((Delta.faceBoundary f).mem_iff d).mpr heq, rfl⟩))
  constructor
  · exact ⟨hface a ha _ (outer_admissible D hsymm Delta hboundary),
      hface _ hreverse _ (outer_admissible D hsymm Delta hboundary)⟩
  · intro C hC
    have hword : RelWord.IsAdmissible D (Delta.faceWord C.face) := by
      rw [DiscDiagram.faceWord, ← Delta.relatorCell_word C hC]
      exact hcells C hC
    exact ⟨hface a ha _ hword, hface _ hreverse _ hword⟩

/-- The nonempty exterior supplies a legal letter even if the group has no
nonidentity element. An empty geodesic is spelled by that letter and its inverse. -/
theorem exists_replacement_word (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (Delta : DiscDiagram.{u, w, v} W)
    (hboundary : RelWord.IsAdmissible D Delta.boundaryWord) (g : G) :
    ∃ word : List (RelLetter G Lambda), word ≠ [] ∧
      RelWord.IsAdmissible D word ∧ RelLetter.listVal word = g := by
  let FB := Delta.faceBoundary Delta.outerFace
  let letter := Delta.label (FB.darts.head FB.nonempty)
  have hletter : D.IsLetter letter :=
    outer_admissible D hsymm Delta hboundary _
      (List.mem_map.mpr ⟨_, List.head_mem FB.nonempty, rfl⟩)
  obtain ⟨s, hs, hvalue, _hlen⟩ := OsinComponents.existsGeodesicWord D 1 g
  refine ⟨NonemptyConnectorWord.word letter s,
    NonemptyConnectorWord.nonempty letter s,
    NonemptyConnectorWord.admissible D hsymm letter hletter s hs, ?_⟩
  rw [NonemptyConnectorWord.value]
  simpa only [one_mul] using hvalue

/-- Construct legal labels by repeatedly subdividing illegal G--G edges.
No legality is assumed on the other internal edges during a repair. -/
theorem exists_output (D : RelGenSet G Lambda)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) (Delta : DiscDiagram.{u, w, v} W)
    (hboundary : RelWord.IsAdmissible D Delta.boundaryWord)
    (hcells : ∀ C ∈ Delta.relatorCells, RelWord.IsAdmissible D C.word) :
    Nonempty (Output D Delta) := by
  classical
  suffices ∀ n : ℕ, ∀ Xi : DiscDiagram.{u, w, v} W,
      (illegalDarts D Xi).card = n → RelWord.IsAdmissible D Xi.boundaryWord →
      (∀ C ∈ Xi.relatorCells, RelWord.IsAdmissible D C.word) →
      Nonempty (Output D Xi) from this _ Delta rfl hboundary hcells
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Xi hn hboundary hcells
    by_cases hlegal : ∀ d, D.IsLetter (Xi.label d)
    · exact ⟨⟨Xi, DiscExpansion.refl Xi, Surgery.OrderedRCellMap.refl Xi, hlegal⟩⟩
    · obtain ⟨a, ha⟩ := not_forall.mp hlegal
      obtain ⟨houter, havoid⟩ := illegal_faces D hsymm Xi hboundary hcells a ha
      obtain ⟨word, hne, hword, hvalue⟩ :=
        exists_replacement_word D hsymm Xi hboundary (Xi.label a).val
      have hinv : ∀ l ∈ word, D.IsLetter (RelWord.inv l) :=
        fun l hl => isLetter_relWordInv D hsymm (hword l hl)
      obtain ⟨R⟩ := GEdgeWordSubdivision.exists_raw_output word hne Xi a houter havoid hvalue
      have hlt : (illegalDarts D R.diagram).card < n := by
        rw [← hn]
        exact R.illegalDarts_card_lt D hword hinv ha
      have hboundary' : RelWord.IsAdmissible D R.diagram.boundaryWord := by
        rw [R.expansion.outerWord_eq]
        exact hboundary
      have hcells' : ∀ C ∈ R.diagram.relatorCells, RelWord.IsAdmissible D C.word := by
        intro C hC
        rw [R.cells.list_eq] at hC
        obtain ⟨C0, hC0, rfl⟩ := List.mem_map.mp hC
        rw [R.cells.word_eq]
        exact hcells C0 hC0
      obtain ⟨T⟩ := ih _ hlt R.diagram rfl hboundary' hcells'
      exact ⟨⟨T.diagram, R.expansion.trans T.expansion,
        R.cells.trans T.cells, T.label_admissible⟩⟩

theorem Output.reduced (D : RelGenSet G Lambda) {Delta : DiscDiagram.{u, w, v} W}
    (R : Output D Delta) (hred : Delta.Reduced) : R.diagram.Reduced :=
  R.expansion.cells.reduced hred

def Output.oEquivalent (D : RelGenSet G Lambda) {Delta : DiscDiagram.{u, w, v} W}
    (R : Output D Delta) : OEquivalentDiscDiagram Delta R.diagram :=
  R.expansion.replacement.oEquivalent

end GroupApproximation.GGT.VanKampen.DiscLabelNormalization

#audit_axioms GroupApproximation.GGT.VanKampen.DiscLabelNormalization.illegal_faces
#audit_axioms GroupApproximation.GGT.VanKampen.DiscLabelNormalization.exists_replacement_word
#audit_axioms GroupApproximation.GGT.VanKampen.DiscLabelNormalization.exists_output
#audit_axioms GroupApproximation.GGT.VanKampen.DiscLabelNormalization.Output.reduced
#audit_axioms GroupApproximation.GGT.VanKampen.DiscLabelNormalization.Output.oEquivalent
