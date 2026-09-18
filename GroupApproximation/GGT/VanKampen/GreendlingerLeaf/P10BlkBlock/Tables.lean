import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.P10BlkBlock.Classes
import GroupApproximation.Meta.AxiomGuard

/-!
# No contiguous removed block on the counterexample pocket

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Lane gl-p10-88.

A lobe colouring of `P10BlkBlockModel.pK` marks a set of faces, given by a table
`T : Fin 7 → Bool` on the face numbers.  Its moved darts are `mvT T`.  The admissible tables are
* `tabA b2 b6`, marking some of the faces `2 = [2,6,10,11]` and `6 = [8,13]` (roots on the walk);
* `tabB c`, marking the one face `c ≠ 1, 3` (a single root off the exterior and the source).

For each of them, no split `cyc = A ++ B ++ C` of the walk has the block shape of
`roseLobeBlk_BlockStatement` (`noBlockA`, `noBlockB`, by `decide +kernel` over the `64`
positions).  `noBlock_of_split` turns an arbitrary split into one at positions `i, j < 8`.

## Manuscript status

Counterexample model for infrastructure of `thm:hull`.  It certifies no printed sentence on its
own.
-/

namespace GroupApproximation.GGT.VanKampen.P10BlkBlockModel

/-- The face number of the reverse of each dart. -/
def cidA : Fin 16 → Fin 7 := ![1, 0, 3, 2, 4, 0, 5, 2, 4, 6, 2, 2, 6, 5, 0, 1]

theorem faceClass_alpha : ∀ x : diagram.toCombMap.Dart,
    faceClass (diagram.toCombMap.alpha x) = cidA x := by
  decide

/-- The moved darts of the face table `T`: neither side is marked. -/
def mvT (T : Fin 7 → Bool) (x : Fin 16) : Bool := !T (faceClass x) && !T (cidA x)

/-- The block clause of `roseLobeBlk_BlockStatement` for the moved darts `mvT T`. -/
abbrev blockAt (T : Fin 7 → Bool) (A B C : List (Fin 16)) : Prop :=
  (B.filter (mvT T) = [] ∧ (A ++ C).filter (mvT T) = A ++ C ∧ A ++ C ≠ []) ∨
    (B.filter (mvT T) = B ∧ (A ++ C).filter (mvT T) = [] ∧ B ≠ [])

/-- Roots on the walk: some of the faces `2` and `6` are marked. -/
def tabA (b2 b6 : Bool) : Fin 7 → Bool := ![false, false, b2, false, false, false, b6]

/-- One root: exactly the face `c` is marked. -/
def tabB (c k : Fin 7) : Bool := decide (c = k)

theorem noBlockA (b2 b6 : Bool) (h : (b2 || b6) = true) : ∀ i < 8, ∀ j < 8,
    ¬blockAt (tabA b2 b6) (cyc.take i) ((cyc.drop i).take j) ((cyc.drop i).drop j) := by
  cases b2 <;> cases b6
  · exact absurd h (by decide)
  all_goals decide +kernel

theorem noBlockB (c : Fin 7) (h1 : c ≠ 1) (h3 : c ≠ 3) : ∀ i < 8, ∀ j < 8,
    ¬blockAt (tabB c) (cyc.take i) ((cyc.drop i).take j) ((cyc.drop i).drop j) := by
  fin_cases c
  · decide +kernel
  · exact (h1 rfl).elim
  · decide +kernel
  · exact (h3 rfl).elim
  · decide +kernel
  · decide +kernel
  · decide +kernel

/-- A split of a list is read off at the lengths of its first two pieces. -/
theorem split3 {α : Type} {l A B C : List α} (h : l = A ++ B ++ C) :
    A = l.take A.length ∧ B = (l.drop A.length).take B.length ∧
      C = (l.drop A.length).drop B.length := by
  subst h
  rw [List.append_assoc, List.take_left, List.drop_left, List.take_left, List.drop_left]
  exact ⟨rfl, rfl, rfl⟩

/-- **No split of the walk is a block**, once no split at positions `i, j < 8` is. -/
theorem noBlock_of_split (T : Fin 7 → Bool) (hT : ∀ i < 8, ∀ j < 8,
    ¬blockAt T (cyc.take i) ((cyc.drop i).take j) ((cyc.drop i).drop j))
    {A B C : List (Fin 16)} (h : cyc = A ++ B ++ C) : ¬blockAt T A B C := by
  obtain ⟨hA, hB, hC⟩ := split3 h
  have h1 := congrArg List.length h
  rw [List.length_append, List.length_append] at h1
  have h7 : cyc.length = 7 := rfl
  have hi : A.length < 8 := by omega
  have hj : B.length < 8 := by omega
  have hb := hT A.length hi B.length hj
  rwa [← hA, ← hB, ← hC] at hb

end GroupApproximation.GGT.VanKampen.P10BlkBlockModel

#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.cidA
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.faceClass_alpha
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.mvT
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.blockAt
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.tabA
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.tabB
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.noBlockA
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.noBlockB
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.split3
#audit_axioms GroupApproximation.GGT.VanKampen.P10BlkBlockModel.noBlock_of_split
