import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSameCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassRunPositions
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: list and `runPos` steps for the head split

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-04`, first module.
The head split (`Piece04.WindowShape.WindowHeadSplit`) walks the sides `s :: L` of a class along
`OsinLemma94ClassPolygons.runPos`.  This module gives the one-step facts it uses.

* `drop_append_add`, `drop_append_add_of_eq`, `drop_append_of_length_le`: dropping past a first
  block.
* `runPos_cons_of_le`, `runPos_cons_of_mid`, `runPos_cons_of_gt`: the three branches of the
  `runPos` if-cascade at a side `s` of word length `ℓ` and gap word length `γ`: `x ≤ ℓ` gives `x`,
  `ℓ < x ≤ ℓ + γ` gives `ℓ`, and `ℓ + γ < x` recurses.
* `runPos_cons_le_of_le`: at `y ≤ ℓ + γ` the side-run position is at most `ℓ`.
* `lt_of_runPos_lt`: `runPos` is monotone, so a strict increase of `runPos` forces `x < y`.
* `exists_next_side`: sides with a positive side-run position are a nonempty list whose first side
  has a first dart (sides are nonempty).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit

universe u w v

/-- Dropping the length of a first block plus `i` drops `i` from the second block. -/
theorem drop_append_add {α : Type*} (l₁ l₂ : List α) (i : ℕ) :
    (l₁ ++ l₂).drop (l₁.length + i) = l₂.drop i := by
  rw [List.drop_append, List.drop_of_length_le (Nat.le_add_right l₁.length i), List.nil_append,
    Nat.add_sub_cancel_left]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.drop_append_add

/-- `drop_append_add`, with the length of the first block given by an equation. -/
theorem drop_append_add_of_eq {α : Type*} {l₁ l₂ : List α} {m : ℕ} (h : l₁.length = m) (i : ℕ) :
    (l₁ ++ l₂).drop (m + i) = l₂.drop i := by
  subst h
  exact drop_append_add l₁ l₂ i

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.drop_append_add_of_eq

/-- Dropping at least the first block drops the rest from the second block. -/
theorem drop_append_of_length_le {α : Type*} {l₁ l₂ : List α} {i : ℕ} (h : l₁.length ≤ i) :
    (l₁ ++ l₂).drop i = l₂.drop (i - l₁.length) := by
  rw [List.drop_append, List.drop_of_length_le h, List.nil_append]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.drop_append_of_length_le

section RunPosSteps

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- Inside the first side word, the side-run position is the position. -/
theorem runPos_cons_of_le (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (s : ℕ)
    (L : List ℕ) (x : ℕ) (h : x ≤ (P.word k s).length) : Q.runPos k (s :: L) x = x := by
  rw [OsinLemma94ClassPolygons.runPos, if_pos h]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.runPos_cons_of_le

/-- Across the first gap, the side-run position is the end of the first side word. -/
theorem runPos_cons_of_mid (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (s : ℕ)
    (L : List ℕ) (x : ℕ) (h1 : ¬ x ≤ (P.word k s).length)
    (h2 : x ≤ (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) :
    Q.runPos k (s :: L) x = (P.word k s).length := by
  rw [OsinLemma94ClassPolygons.runPos, if_neg h1, if_pos h2]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.runPos_cons_of_mid

/-- Past the first side and its gap, the side-run position recurses. -/
theorem runPos_cons_of_gt (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (s : ℕ)
    (L : List ℕ) (x : ℕ)
    (h : ¬ x ≤ (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) :
    Q.runPos k (s :: L) x = (P.word k s).length +
      Q.runPos k L
        (x - (P.word k s).length - (Embedded.dartWord S.diagram (Q.gap k s)).length) := by
  have h1 : ¬ x ≤ (P.word k s).length := by omega
  rw [OsinLemma94ClassPolygons.runPos, if_neg h1, if_neg h]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.runPos_cons_of_gt

/-- Up to the end of the first gap, the side-run position is at most the first side length. -/
theorem runPos_cons_le_of_le (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (s : ℕ)
    (L : List ℕ) (y : ℕ)
    (h : y ≤ (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) :
    Q.runPos k (s :: L) y ≤ (P.word k s).length := by
  rw [OsinLemma94ClassPolygons.runPos]
  split_ifs <;> omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.runPos_cons_le_of_le

/-- A strict increase of the side-run position forces a strict increase of the position. -/
theorem lt_of_runPos_lt (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (L : List ℕ)
    (x y : ℕ) (h : Q.runPos k L x < Q.runPos k L y) : x < y := by
  by_contra hge
  have hmono := Q.runPos_mono k L (Nat.le_of_not_lt hge)
  omega

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.lt_of_runPos_lt

/-- Sides with a positive side-run position start with a side, and that side has a first dart. -/
theorem exists_next_side (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (L : List ℕ) (y : ℕ)
    (hne : ∀ s ∈ L, P.sideDarts k s ≠ []) (h : 0 < Q.runPos k L y) :
    ∃ (s' : ℕ) (L'' : List ℕ) (t : S.diagram.toCombMap.Dart)
      (R' : List S.diagram.toCombMap.Dart), L = s' :: L'' ∧ P.sideDarts k s' = t :: R' := by
  cases L with
  | nil => simp [OsinLemma94ClassPolygons.runPos] at h
  | cons s' L'' =>
    obtain ⟨t, R', hR'⟩ := List.exists_cons_of_ne_nil (hne s' List.mem_cons_self)
    exact ⟨s', L'', t, R', rfl, hR'⟩

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit.exists_next_side

end RunPosSteps

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowHeadSplit
