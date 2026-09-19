import GroupApproximation.GGT.VanKampen.CactusZeroBoundary
import GroupApproximation.GGT.HullSCRelatorAdmissible

/-!
# Filling a nonempty null relative word by one G-cell

The polygon and its two face traversals are constructed explicitly. No
relator cells are introduced. The exterior boundary is exactly the requested
relative word, including its distinction between base and peripheral letters.
This is the disc used for ambient-group padding in Osin's argument; gluing it
into a pre-existing diagram is a separate operation.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.HullSC
open GroupApproximation.HullSC.Lemma44OrientedRelatorDiagram

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

namespace NullWordDisc

/-- The polygon shape for a prescribed forward outer-face word. -/
def shape (word : List (RelLetter G Lambda)) (hne : word ≠ []) : CactusShape where
  boundaryLength := word.length
  boundary_pos := by
    cases word with
    | nil => exact False.elim (hne rfl)
    | cons a word => exact Nat.zero_lt_succ _
  cellCount := 0
  relatorLength := Fin.elim0
  relator_pos := by intro i; exact Fin.elim0 i

def label (word : List (RelLetter G Lambda)) (hne : word ≠ []) :
    (shape word hne).toCombMap.Dart → RelLetter G Lambda
  | .outerForward j => word.get j
  | .outerBackward j => RelWord.inv (word.get j)
  | .relatorForward i _ => Fin.elim0 i
  | .relatorBackward i _ => Fin.elim0 i
  | .stemOut i => Fin.elim0 i
  | .stemIn i => Fin.elim0 i

theorem label_alpha (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (d : CactusDart (shape word hne)) :
    label word hne ((shape word hne).toCombMap.alpha d) = RelWord.inv (label word hne d) := by
  cases d with
  | outerForward j => rfl
  | outerBackward j => exact (RelWord.inv_inv_letter _).symm
  | relatorForward i j => exact Fin.elim0 i
  | relatorBackward i j => exact Fin.elim0 i
  | stemOut i => exact Fin.elim0 i
  | stemIn i => exact Fin.elim0 i

/-- Use the explicit backwards boundary on the unique inner face. -/
noncomputable def faceBoundary (word : List (RelLetter G Lambda)) (hne : word ≠ [])
    (f : (shape word hne).toCombMap.Face) : FaceBoundary (shape word hne).toCombMap f := by
  classical
  exact if h : f = (shape word hne).bigFace then
    h.symm ▸ (shape word hne).zeroBigFaceBoundary rfl
  else (shape word hne).faceBoundary f

theorem outer_word (word : List (RelLetter G Lambda)) (hne : word ≠ []) :
    ((faceBoundary word hne (shape word hne).outerFace).darts.map (label word hne)) = word := by
  rw [faceBoundary, dif_neg (shape word hne).bigFace_ne_outerFace.symm,
    CactusShape.faceBoundary_outerFace_darts, cactus_outerBoundary_darts]
  change (List.ofFn (CactusDart.outerForward (S := shape word hne))).map
    (fun d : CactusDart (shape word hne) => label word hne d) = word
  rw [← List.ofFn_comp']
  exact List.ofFn_get word

theorem inner_word (word : List (RelLetter G Lambda)) (hne : word ≠ []) :
    ((faceBoundary word hne (shape word hne).bigFace).darts.map (label word hne)) =
      RelWord.revInv word := by
  rw [faceBoundary, dif_pos rfl]
  change (CactusShape.outerBackwardDarts (shape word hne)).map (label word hne) = _
  rw [CactusShape.outerBackwardDarts]
  change (List.ofFn (fun j : Fin word.length => CactusDart.outerBackward (S := shape word hne) j.rev)).map
    (fun d : CactusDart (shape word hne) => label word hne d) = _
  rw [← List.ofFn_comp']
  change List.ofFn (fun j : Fin word.length => RelWord.inv (word.get j.rev)) = _
  calc
    _ = (List.ofFn (fun j : Fin word.length => RelWord.inv (word.get j))).reverse :=
      ofFn_comp_rev (fun j : Fin word.length => RelWord.inv (word.get j))
    _ = RelWord.revInv (List.ofFn word.get) := by
      rw [RelWord.revInv, ← List.ofFn_comp']
    _ = _ := congrArg RelWord.revInv (List.ofFn_get word)

/-- The explicit disc with no relator faces and one inner G-face. Its outer
face is read forwards as `word`, so its disc boundary is `revInv word`. -/
noncomputable def diagram (W : Set (List (RelLetter G Lambda)))
    (word : List (RelLetter G Lambda)) (hne : word ≠ []) (hval : RelLetter.listVal word = 1) :
    DiscDiagram.{u, w, 0} W where
  toCombMap := (shape word hne).toCombMap
  planar := (shape word hne).planar
  label := label word hne
  label_alpha := label_alpha word hne
  outerFace := (shape word hne).outerFace
  faceBoundary := faceBoundary word hne
  relatorCells := []
  relatorCell_faces_nodup := by simp
  relatorCell_word := by simp
  inner_face := by
    intro f hf
    right
    rw [(shape word hne).face_eq_big_of_ne_outer rfl f hf, inner_word,
      RelWord.listVal_revInv, hval, inv_one]
  boundary_product := by
    rw [outer_word, RelWord.listVal_revInv, hval, inv_one]
    rfl

theorem diagram_boundaryWord (W : Set (List (RelLetter G Lambda)))
    (word : List (RelLetter G Lambda)) (hne : word ≠ []) (hval : RelLetter.listVal word = 1) :
    (diagram W word hne hval).boundaryWord = RelWord.revInv word := by
  change RelWord.revInv
    ((faceBoundary word hne (shape word hne).outerFace).darts.map (label word hne)) = _
  rw [outer_word]

theorem label_admissible {D : RelGenSet G Lambda}
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) {word : List (RelLetter G Lambda)}
    (hword : RelWord.IsAdmissible D word) (hne : word ≠ [])
    (d : CactusDart (shape word hne)) : D.IsLetter (label word hne d) := by
  cases d with
  | outerForward j => exact hword _ (List.get_mem word j)
  | outerBackward j => exact isLetter_relWordInv D hsymm (hword _ (List.get_mem word j))
  | relatorForward i j => exact Fin.elim0 i
  | relatorBackward i j => exact Fin.elim0 i
  | stemOut i => exact Fin.elim0 i
  | stemIn i => exact Fin.elim0 i

end NullWordDisc

/-- Every nonempty admissible word trivial in the ambient group has an
actual reduced G-cell disc with that exact boundary and legal dart labels. -/
def NullWordDiscStatement : Prop :=
  ∀ (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda),
    (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ word : List (RelLetter G Lambda), HullSC.RelWord.IsAdmissible D word →
      word ≠ [] → RelLetter.listVal word = 1 →
      ∀ W : Set (List (RelLetter G Lambda)),
        ∃ Delta : DiscDiagram.{u, w, 0} W,
          Delta.boundaryWord = word ∧ Delta.relatorCells = [] ∧ Delta.Reduced ∧
            (∀ d : Delta.toCombMap.Dart, D.IsLetter (Delta.label d)) ∧
            Delta.toCombMap.faceCount = 2

theorem nullWordDisc : NullWordDiscStatement.{u, w} := by
  intro G _ Lambda D hsymm word hword hne hval W
  have hinv : RelLetter.listVal (RelWord.revInv word) = 1 := by
    rw [RelWord.listVal_revInv, hval, inv_one]
  have hneinv : RelWord.revInv word ≠ [] := by
    intro h
    apply hne
    have hh := congrArg RelWord.revInv h
    rw [RelWord.revInv_revInv] at hh
    exact hh
  let Delta := NullWordDisc.diagram W (RelWord.revInv word) hneinv hinv
  refine ⟨Delta, ?_, rfl, DiscDiagram.reduced_of_no_rCells Delta rfl, ?_, ?_⟩
  · exact (NullWordDisc.diagram_boundaryWord W (RelWord.revInv word) hneinv hinv).trans
      (RelWord.revInv_revInv word)
  · exact NullWordDisc.label_admissible hsymm (isAdmissible_revInv hsymm hword) hneinv
  · change (NullWordDisc.shape (RelWord.revInv word) hneinv).toCombMap.faceCount = 0 + 2
    exact (NullWordDisc.shape (RelWord.revInv word) hneinv).faceCount_eq

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.NullWordDisc.outer_word
#audit_axioms GroupApproximation.GGT.VanKampen.NullWordDisc.inner_word
#audit_axioms GroupApproximation.GGT.VanKampen.NullWordDisc.diagram
#audit_axioms GroupApproximation.GGT.VanKampen.NullWordDisc.label_admissible
#audit_closed_axioms GroupApproximation.GGT.VanKampen.nullWordDisc
