import Mathlib.Data.List.Rotate
import GroupApproximation.GGT.VanKampen.Estimating.OsinPocketCellWalk
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07LakeExclusion.LakeFillArc
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf P07, inner pocket: side chunks bounded by ε (list core)

Lane `gl-p07-11`.  Infrastructure for `P07LakeExclusion.InnerPocketEnclosedTwoArcStatement`
(`GreendlingerLeaf/P07LakeExclusion/InnerTwoArcLong.lean`), towards Osin, arXiv:math/0411039v3,
§9, Lemma 9.7(b) and `thm:hull` (tex 2122/2129).  Certifies no printed sentence on its own.

## Mathematical content

Lane 10 decomposes the inverse outside walk of the lake-filled pocket, after a rotation, as
`R₁ ++ U₁ ++ R₂ ++ U₂`: `U₁`, `U₂` are arc runs, and every dart `r` of `R₁ ++ R₂` has its reverse
`α r` on one of the two far sides `s₁ = a.sideFrom j`, `s₂ = b.sideFrom i`, each of length `≤ ε`.

* The outside walk is duplicate free, hence so is its inverse walk (reversal, then the injective
  `α`), and every chunk of the decomposition.
* **Case (A), each chunk on one far side.**  A duplicate-free chunk whose reverses lie on a list `s`
  is at most as long as `s` (`LakeFill.length_le_of_forall_alpha_mem`: `α` is injective, so the
  reverses form a duplicate-free sub-multiset of `s`).  So `|R₁|, |R₂| ≤ ε`.
* **Case (B), `U₁ = []`.**  The inverse walk is `R₁ ++ R₂ ++ U₂`, and `R₁ ++ R₂` is duplicate free
  with reverses on `s₁ ++ s₂`, so `|R₁ ++ R₂| ≤ 2ε`.  Re-split it at `ε`
  (`LakeFill.exists_split_two`) as `S₁ ++ S₂`: the walk reads `S₁ ++ [] ++ S₂ ++ U₂`.
* **Case (C), `U₂ = []`.**  The inverse walk `R₁ ++ U₁ ++ R₂`, rotated by `|R₁ ++ U₁|`, is
  `R₂ ++ (R₁ ++ U₁)`; a rotation of the inverse walk is the inverse walk of a rotation
  (`exists_rotate_invDarts`).  Re-split `R₂ ++ R₁` as in (B): the walk reads
  `S₁ ++ [] ++ S₂ ++ U₁`, with the empty run first, as the normal form `A₁.length = 0 ∨ …` wants.

The endpoint is `exists_bounded_fourPiece`, fully proved.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound

universe u w v

open Embedded

section Lists

variable {α : Type*}

/-- The first chunk of a duplicate-free four-piece list is duplicate free. -/
theorem nodup_first {R₁ U₁ R₂ U₂ : List α} (h : (R₁ ++ U₁ ++ R₂ ++ U₂).Nodup) : R₁.Nodup :=
  List.Nodup.sublist ((List.sublist_append_left R₁ U₁).trans
    ((List.sublist_append_left (R₁ ++ U₁) R₂).trans
      (List.sublist_append_left (R₁ ++ U₁ ++ R₂) U₂))) h

/-- The third chunk of a duplicate-free four-piece list is duplicate free. -/
theorem nodup_third {R₁ U₁ R₂ U₂ : List α} (h : (R₁ ++ U₁ ++ R₂ ++ U₂).Nodup) : R₂.Nodup :=
  List.Nodup.sublist ((List.sublist_append_right (R₁ ++ U₁) R₂).trans
    (List.sublist_append_left (R₁ ++ U₁ ++ R₂) U₂)) h

/-- The first and third chunks of a duplicate-free four-piece list together are duplicate free. -/
theorem nodup_first_third {R₁ U₁ R₂ U₂ : List α} (h : (R₁ ++ U₁ ++ R₂ ++ U₂).Nodup) :
    (R₁ ++ R₂).Nodup :=
  List.Nodup.sublist (((List.sublist_append_left R₁ U₁).append (List.Sublist.refl R₂)).trans
    (List.sublist_append_left (R₁ ++ U₁ ++ R₂) U₂)) h

end Lists

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {X : DiscDiagram.{u, w, v} W}

/-- **A rotation of the inverse walk is the inverse walk of a rotation.** -/
theorem exists_rotate_invDarts (w : List X.toCombMap.Dart) (m : ℕ) :
    ∃ k, invDarts X (w.rotate k) = (invDarts X w).rotate m := by
  refine ⟨w.length - m % w.length, ?_⟩
  simp only [invDarts]
  rw [← List.rotate_reverse, List.map_rotate]

/-- The inverse walk of a duplicate-free walk is duplicate free. -/
theorem invDarts_nodup {w : List X.toCombMap.Dart} (hw : w.Nodup) : (invDarts X w).Nodup :=
  (List.nodup_reverse.mpr hw).map X.toCombMap.alpha.injective

/-- The inverse walk of a rotation of a duplicate-free walk is duplicate free. -/
theorem rotate_invDarts_nodup {w : List X.toCombMap.Dart} (hw : w.Nodup) (n : ℕ) :
    (invDarts X (w.rotate n)).Nodup :=
  invDarts_nodup (List.nodup_rotate.mpr hw)

/-- **A one-side chunk is at most ε.**  A duplicate-free chunk whose reverses lie on a list of
length at most `ε` has length at most `ε`. -/
theorem chunk_length_le {R s : List X.toCombMap.Dart} {eps : ℕ} (hR : R.Nodup)
    (hs : s.length ≤ eps) (h : ∀ r ∈ R, X.toCombMap.alpha r ∈ s) : R.length ≤ eps :=
  (P07LakeExclusion.LakeFill.length_le_of_forall_alpha_mem hR h).trans hs

/-- **A two-side chunk re-splits at ε.**  A duplicate-free chunk whose reverses lie on two lists of
length at most `ε` splits into two chunks of length at most `ε`. -/
theorem exists_split_chunks {R s₁ s₂ : List X.toCombMap.Dart} {eps : ℕ} (hR : R.Nodup)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    (h : ∀ r ∈ R, X.toCombMap.alpha r ∈ s₁ ∨ X.toCombMap.alpha r ∈ s₂) :
    ∃ S₁ S₂ : List X.toCombMap.Dart, S₁.length ≤ eps ∧ S₂.length ≤ eps ∧ R = S₁ ++ S₂ := by
  have hle : R.length ≤ (s₁ ++ s₂).length :=
    P07LakeExclusion.LakeFill.length_le_of_forall_alpha_mem hR fun r hr =>
      List.mem_append.mpr (h r hr)
  rw [List.length_append] at hle
  exact P07LakeExclusion.LakeFill.exists_split_two (l := R) (n := eps) (by omega)

/-- **Side chunks bounded by ε** (list form).  From a four-piece decomposition of the inverse walk
of a rotation of a duplicate-free walk, whose side chunks reverse darts of two lists of length at
most `ε` (each chunk on one list, or one run empty), a rotation of the walk has a four-piece
decomposition whose side chunks have length at most `ε` and whose runs are the old runs, or the
empty run followed by the old first run when the old second run was empty. -/
theorem exists_bounded_fourPiece {w : List X.toCombMap.Dart} {eps n : ℕ}
    {s₁ s₂ R₁ U₁ R₂ U₂ : List X.toCombMap.Dart} (hw : w.Nodup)
    (hs₁ : s₁.length ≤ eps) (hs₂ : s₂.length ≤ eps)
    (hdec : invDarts X (w.rotate n) = R₁ ++ U₁ ++ R₂ ++ U₂)
    (hcase : (((∀ r ∈ R₁, X.toCombMap.alpha r ∈ s₁) ∨ (∀ r ∈ R₁, X.toCombMap.alpha r ∈ s₂)) ∧
        ((∀ r ∈ R₂, X.toCombMap.alpha r ∈ s₁) ∨ (∀ r ∈ R₂, X.toCombMap.alpha r ∈ s₂))) ∨
      ((∀ r ∈ R₁ ++ R₂, X.toCombMap.alpha r ∈ s₁ ∨ X.toCombMap.alpha r ∈ s₂) ∧
        (U₁ = [] ∨ U₂ = []))) :
    ∃ (m : ℕ) (S₁ V₁ S₂ V₂ : List X.toCombMap.Dart),
      invDarts X (w.rotate m) = S₁ ++ V₁ ++ S₂ ++ V₂ ∧ S₁.length ≤ eps ∧ S₂.length ≤ eps ∧
        ((V₁ = U₁ ∧ V₂ = U₂) ∨ (U₂ = [] ∧ V₁ = [] ∧ V₂ = U₁)) := by
  have hnd : (R₁ ++ U₁ ++ R₂ ++ U₂).Nodup := by
    rw [← hdec]
    exact rotate_invDarts_nodup hw n
  rcases hcase with ⟨h₁, h₂⟩ | ⟨hfar, rfl | rfl⟩
  · refine ⟨n, R₁, U₁, R₂, U₂, hdec, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · rcases h₁ with h | h
      · exact chunk_length_le (nodup_first hnd) hs₁ h
      · exact chunk_length_le (nodup_first hnd) hs₂ h
    · rcases h₂ with h | h
      · exact chunk_length_le (nodup_third hnd) hs₁ h
      · exact chunk_length_le (nodup_third hnd) hs₂ h
  · obtain ⟨S₁, S₂, hS₁, hS₂, hsplit⟩ := exists_split_chunks (nodup_first_third hnd) hs₁ hs₂ hfar
    refine ⟨n, S₁, [], S₂, U₂, ?_, hS₁, hS₂, Or.inl ⟨rfl, rfl⟩⟩
    rw [hdec]
    simp only [List.append_nil]
    rw [hsplit]
  · have hrot : (invDarts X (w.rotate n)).rotate (R₁ ++ U₁).length = R₂ ++ (R₁ ++ U₁) := by
      rw [hdec, List.append_nil]
      exact List.rotate_append_length_eq (R₁ ++ U₁) R₂
    obtain ⟨k, hk⟩ := exists_rotate_invDarts (w.rotate n) (R₁ ++ U₁).length
    rw [hrot, List.rotate_rotate] at hk
    have hnd' : (R₂ ++ R₁).Nodup := by
      have h := rotate_invDarts_nodup (X := X) hw (n + k)
      rw [hk] at h
      exact List.Nodup.sublist ((List.Sublist.refl R₂).append (List.sublist_append_left R₁ U₁)) h
    have hfar' : ∀ r ∈ R₂ ++ R₁,
        X.toCombMap.alpha r ∈ s₁ ∨ X.toCombMap.alpha r ∈ s₂ := fun r hr =>
      hfar r (List.mem_append.mpr (List.mem_append.mp hr).symm)
    obtain ⟨S₁, S₂, hS₁, hS₂, hsplit⟩ := exists_split_chunks hnd' hs₁ hs₂ hfar'
    refine ⟨n + k, S₁, [], S₂, U₁, ?_, hS₁, hS₂, Or.inr ⟨rfl, rfl, rfl⟩⟩
    rw [hk, List.append_nil, ← hsplit, List.append_assoc]

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.nodup_first
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.nodup_third
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.nodup_first_third
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.exists_rotate_invDarts
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.invDarts_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.rotate_invDarts_nodup
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.chunk_length_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.exists_split_chunks
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P07InnerPocket.SideBound.exists_bounded_fourPiece
