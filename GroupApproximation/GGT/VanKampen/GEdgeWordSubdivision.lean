import GroupApproximation.GGT.VanKampen.GEdgeSubdivisionExpansion
import GroupApproximation.GGT.VanKampen.GEdgeRelabel

/-!
# Replacing an interior G-edge by any nonempty admissible word

The output is an actual planar disc, with an actual expansion of every dart
and every face boundary. The chosen edge reads exactly the prescribed word;
every other edge retains its one-letter word. Temporary product letters in
the recursion need not be generators. The final disc has only legal labels.
-/

namespace GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision

open HullSC EdgeSubdivision
universe u w v
variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}

structure Output (D : RelGenSet G Lambda) (Delta : DiscDiagram.{u, w, v} W)
    (a : Delta.toCombMap.Dart) (word : List (RelLetter G Lambda)) where
  diagram : DiscDiagram.{u, w, v} W
  expansion : DiscExpansion Delta diagram
  word_eq : (expansion.darts a).map diagram.label = word
  other_word : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a →
    (expansion.darts d).map diagram.label = [Delta.label d]
  label_admissible : ∀ d, D.IsLetter (diagram.label d)

theorem exists_output (D : RelGenSet G Lambda) (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (hword : ∀ letter ∈ word, D.IsLetter letter)
    (Delta : DiscDiagram.{u, w, v} W) (a : Delta.toCombMap.Dart)
    (houter : Delta.toCombMap.faceOf a ≠ Delta.outerFace ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ Delta.outerFace)
    (hcells : ∀ C ∈ Delta.relatorCells, Delta.toCombMap.faceOf a ≠ C.face ∧
      Delta.toCombMap.faceOf (Delta.toCombMap.alpha a) ≠ C.face)
    (hlabel : ∀ d, d ≠ a → d ≠ Delta.toCombMap.alpha a → D.IsLetter (Delta.label d))
    (hvalue : RelLetter.listVal word = (Delta.label a).val) :
    Nonempty (Output D Delta a word) := by
  classical
  induction word generalizing Delta with
  | nil => exact (hne rfl).elim
  | cons letter tail ih =>
      have hletter : D.IsLetter letter := hword letter List.mem_cons_self
      by_cases htail : tail = []
      · subst tail
        have hv : letter.val = (Delta.label a).val := by simpa [RelLetter.listVal] using hvalue
        refine ⟨{
          diagram := GEdgeRelabel.diagram Delta a letter houter hcells hv
          expansion := GEdgeRelabel.expansion Delta a letter houter hcells hv
          word_eq := ?_
          other_word := ?_
          label_admissible := GEdgeRelabel.label_admissible Delta a letter D hsymm hlabel hletter }⟩
        · change [GEdgeRelabel.label Delta a letter a] = [letter]
          exact congrArg List.singleton (GEdgeRelabel.label_at Delta a letter)
        · intro d ha hb
          change [GEdgeRelabel.label Delta a letter d] = [Delta.label d]
          exact congrArg List.singleton (GEdgeRelabel.label_other Delta a letter d ha hb)
      · let right : RelLetter G Lambda := .base (RelLetter.listVal tail)
        have hfactor : (Delta.label a).val = letter.val * right.val := by
          exact hvalue.symm.trans (RelWord.listVal_cons letter tail)
        let Xi := GEdgeSubdivision.diagram Delta a houter hcells letter right hfactor
        let b : Xi.toCombMap.Dart := embed Delta.toCombMap a
        have hbvalue : RelLetter.listVal tail = (Xi.label b).val :=
          (congrArg RelLetter.val
            (GEdgeSubdivision.remaining_label Delta a houter hcells letter right hfactor)).symm
        obtain ⟨R⟩ := ih htail (fun l hl => hword l (List.mem_cons_of_mem letter hl)) Xi b
          (GEdgeSubdivision.remaining_outer Delta a houter)
          (GEdgeSubdivision.remaining_cells Delta a houter hcells letter right hfactor)
          (GEdgeSubdivision.label_away_remaining Delta a houter hcells letter right hfactor
            D hsymm hlabel hletter) hbvalue
        let E := GEdgeSubdivision.expansion Delta a houter hcells letter right hfactor
        let expandR : EdgeSubdivision.Dart Delta.toCombMap → List R.diagram.toCombMap.Dart := R.expansion.darts
        refine ⟨{
          diagram := R.diagram
          expansion := E.trans R.expansion
          word_eq := ?_
          other_word := ?_
          label_admissible := R.label_admissible }⟩
        · change ((expand Delta.toCombMap a a).flatMap expandR).map R.diagram.label = _
          have hexpand : expand Delta.toCombMap a a = [none, embed Delta.toCombMap a] := by simp [expand]
          rw [hexpand, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append]
          have hfirst := R.other_word (none : Xi.toCombMap.Dart)
            (by change (none : EdgeSubdivision.Dart Delta.toCombMap) ≠ some (some a); intro h; cases h)
            (by change (none : EdgeSubdivision.Dart Delta.toCombMap) ≠ some (some (Delta.toCombMap.alpha a)); intro h; cases h)
          exact (congrArg₂ List.append hfirst R.word_eq).trans rfl
        · intro d ha hb
          change ((expand Delta.toCombMap a d).flatMap expandR).map R.diagram.label = _
          have hexpand : expand Delta.toCombMap a d = [embed Delta.toCombMap d] := by simp [expand, ha, hb]
          rw [hexpand, List.flatMap_singleton]
          have hda : embed Delta.toCombMap d ≠ b := by
            intro h
            exact ha (Option.some.inj (Option.some.inj h))
          have hdb : embed Delta.toCombMap d ≠ Xi.toCombMap.alpha b := by
            intro h
            exact hb (Option.some.inj (Option.some.inj h))
          refine (R.other_word (embed Delta.toCombMap d) hda hdb).trans ?_
          change [subdivideLabel Delta.toCombMap a Delta.label letter right (embed Delta.toCombMap d)] = [Delta.label d]
          simp only [subdivideLabel, embed, EdgeInsertion.embed, if_neg ha, if_neg hb]

theorem Output.length_eq {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
    {a : Delta.toCombMap.Dart} {word : List (RelLetter G Lambda)} (R : Output D Delta a word) :
    (R.expansion.darts a).length = word.length := by
  simpa only [List.length_map] using congrArg List.length R.word_eq

theorem Output.nodup {D : RelGenSet G Lambda} {Delta : DiscDiagram.{u, w, v} W}
    {a : Delta.toCombMap.Dart} {word : List (RelLetter G Lambda)} (R : Output D Delta a word) :
    (R.expansion.darts a).Nodup := by
  simpa only [List.flatMap_singleton] using R.expansion.nodup [a] (List.nodup_singleton a)

end GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision

#audit_axioms GroupApproximation.GGT.VanKampen.GEdgeWordSubdivision.exists_output
