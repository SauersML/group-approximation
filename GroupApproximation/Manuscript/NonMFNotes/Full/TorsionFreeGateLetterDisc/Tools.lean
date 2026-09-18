import GroupApproximation.Manuscript.NonMFNotes.Full.TorsionFreeGateVK.LetterDisc
import GroupApproximation.Meta.AxiomGuard

/-!
# Realizing words by letter discs

`Realizes R W n` says that some letter disc (`LetterDisc R W`) with boundary word `W` has at
most `n` faces.  This file provides the bookkeeping used by the construction of letter discs
(Lyndon–Schupp, Ch. V §1, Thm. 1.1):

* `face_word_of_cover`, `realizes_of_cover`: to build a letter disc it suffices that every
  dart off the outer face lies on some face cycle reading a word of the symmetrization;
* `LetterDisc.cover`: conversely every letter disc has this property;
* `Realizes.rotate`, `Realizes.rotate_append`: the boundary word may be rotated.

Part of thm:torsionfree (non_mf_group_notes.tex), L7 milestone 1, WO NN07aVK-P1.
-/

namespace GroupApproximation.Full.NN07a.VK

open GroupApproximation.SmallCancellationRouter GroupApproximation.GGT.VanKampen

universe u

set_option linter.unusedSectionVars false

variable {α : Type u} {R : Set (List (α × Bool))}

/-- Rotating a face cycle does not change the face of its head. -/
theorem faceOf_head_rotate {M : CombMap.{0}} {l : List M.Dart} (hl : M.IsFaceCycle l)
    (k : ℕ) :
    M.faceOf ((l.rotate k).head (hl.rotate k).ne_nil) = M.faceOf (l.head hl.ne_nil) :=
  (hl.mem_iff _).mp (List.mem_rotate.mp (List.head_mem _))

/-- If every dart off the outer face lies on a face cycle reading a word of the
symmetrization, then every face cycle off the outer face does. -/
theorem face_word_of_cover {M : CombMap.{0}} (label : M.Dart → α × Bool)
    {outer : List M.Dart} (houter : M.IsFaceCycle outer)
    (hcover : ∀ d : M.Dart, M.faceOf d ≠ M.faceOf (outer.head houter.ne_nil) →
      ∃ l : List M.Dart, M.IsFaceCycle l ∧ d ∈ l ∧ l.map label ∈ symmetrization R)
    (l : List M.Dart) (hl : M.IsFaceCycle l)
    (hne : M.faceOf (l.head hl.ne_nil) ≠ M.faceOf (outer.head houter.ne_nil)) :
    l.map label ∈ symmetrization R := by
  obtain ⟨l₀, hl₀, hmem, hw⟩ := hcover _ hne
  have hface : M.faceOf (l₀.head hl₀.ne_nil) = M.faceOf (l.head hl.ne_nil) :=
    ((hl₀.mem_iff _).mp hmem).symm
  obtain ⟨k, -, hk⟩ := hl₀.exists_rotate_eq hl hface
  rw [← hk, List.map_rotate]
  exact rotate_mem_symmetrization hw k

/-- Some letter disc with boundary word `W` has at most `n` faces. -/
def Realizes (R : Set (List (α × Bool))) (W : List (α × Bool)) (n : ℕ) : Prop :=
  ∃ D : LetterDisc R W, D.map.faceCount ≤ n

theorem Realizes.mono {W : List (α × Bool)} {n n' : ℕ} (h : Realizes R W n) (hn : n ≤ n') :
    Realizes R W n' := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, hD.trans hn⟩

/-- Build a letter disc from a covering family of face cycles. -/
theorem realizes_of_cover {W : List (α × Bool)} {n : ℕ} (M : CombMap.{0})
    (hM : M.IsPlanar) (label : M.Dart → α × Bool)
    (hlabel : ∀ d, label (M.alpha d) = invLetter (label d))
    (outer : List M.Dart) (houter : M.IsFaceCycle outer) (hword : outer.map label = W)
    (hcover : ∀ d : M.Dart, M.faceOf d ≠ M.faceOf (outer.head houter.ne_nil) →
      ∃ l : List M.Dart, M.IsFaceCycle l ∧ d ∈ l ∧ l.map label ∈ symmetrization R)
    (hcount : M.faceCount ≤ n) : Realizes R W n :=
  ⟨{ map := M
     planar := hM
     label := label
     label_alpha := hlabel
     outer := outer
     outer_cycle := houter
     outer_word := hword
     face_word := face_word_of_cover label houter hcover }, hcount⟩

/-- Every dart off the outer face of a letter disc lies on a face cycle reading a word of
the symmetrization. -/
theorem LetterDisc.cover {W : List (α × Bool)} (D : LetterDisc R W) (d : D.map.Dart)
    (hd : D.map.faceOf d ≠ D.map.faceOf (D.outer.head D.outer_cycle.ne_nil)) :
    ∃ l : List D.map.Dart, D.map.IsFaceCycle l ∧ d ∈ l ∧ l.map D.label ∈ symmetrization R := by
  obtain ⟨l, hl, hhead⟩ := D.map.exists_isFaceCycle_head d
  refine ⟨l, hl, ?_, D.face_word l hl ?_⟩
  · rw [← hhead]
    exact List.head_mem _
  · rw [hhead]
    exact hd

theorem LetterDisc.realizes_rotate {W : List (α × Bool)} (D : LetterDisc R W) (k : ℕ) :
    Realizes R (W.rotate k) D.map.faceCount :=
  realizes_of_cover D.map D.planar D.label D.label_alpha (D.outer.rotate k)
    (D.outer_cycle.rotate k) (by rw [List.map_rotate, D.outer_word])
    (fun d hd => D.cover d (by rwa [faceOf_head_rotate] at hd)) le_rfl

/-- Rotating the boundary word. -/
theorem Realizes.rotate {W : List (α × Bool)} {n : ℕ} (h : Realizes R W n) (k : ℕ) :
    Realizes R (W.rotate k) n := by
  obtain ⟨D, hD⟩ := h
  exact (D.realizes_rotate k).mono hD

/-- Exchanging the two halves of the boundary word. -/
theorem Realizes.rotate_append {A B : List (α × Bool)} {n : ℕ} (h : Realizes R (A ++ B) n) :
    Realizes R (B ++ A) n := by
  have h' := h.rotate A.length
  rwa [List.rotate_append_length_eq] at h'

end GroupApproximation.Full.NN07a.VK

#audit_axioms GroupApproximation.Full.NN07a.VK.realizes_of_cover
#audit_axioms GroupApproximation.Full.NN07a.VK.Realizes.rotate_append
