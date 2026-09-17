import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures.Enclosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Charging value failures to relator cells

Every finite set `E` of value failure darts has at most `rCellCount` elements.  Each `e ∈ E` is
charged a private relator cell face in its lobe: when no other dart of `E` lies in the gap of `e`,
any cell of the lobe; otherwise the cell adjacent to the face of a dart `e₁ ∈ E` in the gap of `e`
of largest span.  Private faces of distinct darts differ: nested gaps are separated by the
maximality of the span, and disjoint gaps have disjoint lobes (`lobe_disjoint`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures

open Equiv GroupApproximation.GGT.VanKampen.Embedded SimpleClosedWalkSides FirstTurnEnclosure
open scoped Classical

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}

/-- A value failure in the gap of another has a smaller span. -/
theorem span_lt_of_nested (X : DiscDiagram.{u, w, v} W) {e₁ e₂ : X.toCombMap.Dart}
    (hG₁ : IsValueFailure X e₁) (hG₂ : IsValueFailure X e₂) (hin : e₁ ∈ gap X e₂) :
    idx X (X.toCombMap.facePerm e₁) - idx X e₁ < idx X (X.toCombMap.facePerm e₂) - idx X e₂ := by
  obtain ⟨-, h₁a, h₁b⟩ := (mem_gap_iff X e₂ e₁).mp hin
  obtain ⟨-, -, h₂b⟩ := (mem_gap_iff X e₂ _).mp (facePerm_mem_gap X hG₂ hG₁ hin)
  omega

/-- **A private cell face** for a value failure dart of `E`: a relator cell face in its lobe, off
the lobes of the darts of `E` in its gap. -/
theorem exists_private_face (X : DiscDiagram.{u, w, v} W) {E : Finset X.toCombMap.Dart}
    (hE : ∀ e ∈ E, IsValueFailure X e) {e : X.toCombMap.Dart} (he : e ∈ E) :
    ∃ f, f ∈ lobe X e ∧ (∃ C ∈ X.relatorCells, C.face = f) ∧
      ∀ e₂ ∈ E, e₂ ∈ gap X e → f ∉ lobe X e₂ := by
  have hG := hE e he
  by_cases hne : (E.filter fun e₂ => e₂ ∈ gap X e).Nonempty
  · obtain ⟨e₁, he₁, hmax⟩ :=
      Finset.exists_max_image _ (fun e₂ => idx X (X.toCombMap.facePerm e₂) - idx X e₂) hne
    rw [Finset.mem_filter] at he₁
    have hG₁ := hE e₁ he₁.1
    obtain ⟨x, hx, C, hC, hxC⟩ := hG₁.2.2.2.2
    refine ⟨C.face, ?_, ⟨C, hC, rfl⟩, fun e₂ he₂ hgap₂ hmem => ?_⟩
    · have hx₀ : X.toCombMap.faceOf x ∈ lobe X e := by
        rw [hx]
        exact faceOf_mem_lobe_of_mem_gap X he₁.2 hG₁.2.2.1
      have hk := not_walkKeep_of_faces X e (z := x) (by rw [hx]; exact hG₁.2.2.1)
        (by rw [hxC]; exact C.face_ne_outer)
      have h := faceOf_alpha_mem_enclosedFaces hk hx₀
      rwa [hxC] at h
    · have hG₂ := hE e₂ he₂
      have hspan : idx X (X.toCombMap.facePerm e₂) - idx X e₂ ≤
          idx X (X.toCombMap.facePerm e₁) - idx X e₁ :=
        hmax e₂ (Finset.mem_filter.mpr ⟨he₂, hgap₂⟩)
      have hk := not_walkKeep_of_faces X e₂ (z := X.toCombMap.alpha x)
        (by rw [hxC]; exact C.face_ne_outer)
        (by rw [X.toCombMap.alpha_involutive x, hx]; exact hG₁.2.2.1)
      have h := faceOf_alpha_mem_enclosedFaces hk (by rw [hxC]; exact hmem)
      rw [X.toCombMap.alpha_involutive x, hx] at h
      have hlt := span_lt_of_nested X hG₁ hG₂ (mem_gap_of_faceOf_mem_lobe X hG₂ h hG₁.1 hG₁.2.2.1)
      omega
  · obtain ⟨C, hC, hmem⟩ := exists_cell_mem_lobe X hG
    exact ⟨C.face, hmem, ⟨C, hC, rfl⟩,
      fun e₂ he₂ hgap₂ _ => hne ⟨e₂, Finset.mem_filter.mpr ⟨he₂, hgap₂⟩⟩⟩

/-- The chosen private face (the outer face off `E`). -/
noncomputable def privateFace (X : DiscDiagram.{u, w, v} W) (E : Finset X.toCombMap.Dart)
    (e : X.toCombMap.Dart) : X.toCombMap.Face :=
  if h : (∀ e ∈ E, IsValueFailure X e) ∧ e ∈ E then
    Classical.choose (exists_private_face X h.1 h.2)
  else X.outerFace

theorem privateFace_spec (X : DiscDiagram.{u, w, v} W) {E : Finset X.toCombMap.Dart}
    (hE : ∀ e ∈ E, IsValueFailure X e) {e : X.toCombMap.Dart} (he : e ∈ E) :
    privateFace X E e ∈ lobe X e ∧ (∃ C ∈ X.relatorCells, C.face = privateFace X E e) ∧
      ∀ e₂ ∈ E, e₂ ∈ gap X e → privateFace X E e ∉ lobe X e₂ := by
  unfold privateFace
  split_ifs with h'
  · exact Classical.choose_spec (exists_private_face X h'.1 h'.2)
  · exact absurd ⟨hE, he⟩ h'

theorem privateFace_injOn (X : DiscDiagram.{u, w, v} W) {E : Finset X.toCombMap.Dart}
    (hE : ∀ e ∈ E, IsValueFailure X e) : Set.InjOn (privateFace X E) E := by
  intro e₁ he₁ e₂ he₂ hf
  by_contra hne
  rw [Finset.mem_coe] at he₁ he₂
  have hs₁ := privateFace_spec X hE he₁
  have hs₂ := privateFace_spec X hE he₂
  by_cases h₁ : e₂ ∈ gap X e₁
  · exact hs₁.2.2 e₂ he₂ h₁ (by rw [hf]; exact hs₂.1)
  · by_cases h₂ : e₁ ∈ gap X e₂
    · exact hs₂.2.2 e₁ he₁ h₂ (by rw [← hf]; exact hs₁.1)
    · exact lobe_disjoint X (hE e₁ he₁) (hE e₂ he₂)
        (gap_disjoint X (hE e₁ he₁) (hE e₂ he₂) hne h₁ h₂) hs₁.1 (by rw [hf]; exact hs₂.1)

/-- **Value failure darts are at most the relator cells.** -/
theorem card_le_rCellCount (X : DiscDiagram.{u, w, v} W) (E : Finset X.toCombMap.Dart)
    (hE : ∀ e ∈ E, IsValueFailure X e) : E.card ≤ X.rCellCount := by
  have hmaps : Set.MapsTo (privateFace X E) E
      (X.relatorCells.map RelatorCell.face).toFinset := by
    intro e he
    obtain ⟨C, hC, hCf⟩ := (privateFace_spec X hE (Finset.mem_coe.mp he)).2.1
    rw [Finset.mem_coe, List.mem_toFinset, ← hCf]
    exact List.mem_map_of_mem hC
  calc E.card ≤ (X.relatorCells.map RelatorCell.face).toFinset.card :=
        Finset.card_le_card_of_injOn _ hmaps (privateFace_injOn X hE)
    _ ≤ (X.relatorCells.map RelatorCell.face).length := List.toFinset_card_le _
    _ = X.rCellCount := List.length_map _

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P01ValueFailures
