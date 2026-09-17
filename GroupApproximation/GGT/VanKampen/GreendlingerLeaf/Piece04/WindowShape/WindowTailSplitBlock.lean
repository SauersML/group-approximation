import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassSameCell
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassRunPositions
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: the tail split at one side block

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-05`, first module.
The endpoint `WindowShape.WindowTailSplit.split` (module `WindowShape.WindowTailSplit`) says that a
nonempty run window `[x, y]` whose end `y` is not strictly inside a gap ends with a dart `u`, and
that the class window is `rest ++ u :: γc`, with `γc` empty or the whole gap after the side of `u`.

## The mathematical proof

Write `B = classDarts k i = ⨆_{s ∈ L} (side_s ++ gap_s)` and `R = sideRun k i = ⨆_{s ∈ L} side_s`,
with `L = classSides k i`, and `ρ = runPos k L`.  Every side is nonempty (`side_ne_nil`) and the
gap of the last side is empty (`gap_last`).

1. *The block of `y`.*  Walk the blocks `side_s ++ gap_s` of `L`.  Since `y ≤ |B|` and `y` is not
   strictly inside a gap, exactly one of these happens at the first block with `y ≤ |side_s| +
   |gap_s|` (after subtracting the lengths of the earlier blocks):
   * (a) `0 < y ≤ |side_s|`: then `B.take y = pre ++ u :: []` with `u = side_s[y - 1]`, and
     `ρ y = off + y` with `R[ρ y - 1] = u`;
   * (b) `y = |side_s| + |gap_s|`: then `B.take y = pre ++ u :: gap_s` with `u = side_s.last`, and
     `ρ y = off + |side_s|` with `R[ρ y - 1] = u`.  If `gap_s ≠ []`, then `s` is not the last
     side, so a next side `s'` exists and `B[y] = side_s'.head`.
   In both cases `ρ (|pre| + 1) = ρ y`.  The case `y = 0` of (a) is excluded by `0 < ρ y`.
   This is `TailSplitAt` (this module for one block, `WindowTailSplitCore.tailSplitAt` by
   recursion over `L`).
2. *The window.*  The run window is nonempty, so `ρ x < ρ y` and `0 < ρ y`.  If `|pre| + 1 ≤ x`,
   monotonicity of `ρ` gives `ρ y = ρ (|pre| + 1) ≤ ρ x`, a contradiction, so `x ≤ |pre|`.  Then
   `classWindow = (B.take y).drop x = pre.drop x ++ u :: γc`, and the run window
   `(R.drop (ρ x)).take (ρ y - ρ x)` ends with `R[ρ y - 1] = u`.
3. *The gap case.*  If `γc = gap_s ≠ []`, the last dart `g` of `γc` is the last dart of
   `B.take y`, which is `B[y - 1]`, and `B[y] = e = side_s'.head`, with `s`, `s'` consecutive in
   `L`.

## This module

* `take_drop_eq_append_last`: a nonempty window ends with the entry before its end.
* `TailSplitAt`: the conclusion of step 1 over a list of sides.
* `tailSplitAt_first`, `tailSplitAt_end`: cases (a) and (b) at the first block.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowTailSplit

universe u w v

/-- A nonempty window `(l.drop m).take (n - m)` ends with the entry of `l` at `n - 1`. -/
theorem take_drop_eq_append_last {α : Type*} {l : List α} {m n : ℕ} {u : α} (hmn : m < n)
    (h : l[n - 1]? = some u) : ∃ U' : List α, (l.drop m).take (n - m) = U' ++ [u] := by
  obtain ⟨t, ht⟩ : ∃ t, n - m = t + 1 := ⟨n - m - 1, by omega⟩
  refine ⟨(l.drop m).take t, ?_⟩
  have hmt : m + t = n - 1 := by omega
  rw [ht, List.take_add_one, List.getElem?_drop, hmt, h, Option.toList_some]

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowTailSplit.take_drop_eq_append_last

section Block

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **The tail split at position `y` over the sides `L`** (step 1 of the proof).  The first `y`
darts of the blocks are `pre ++ u :: γc`, `u` is the last dart of the side-run prefix, the position
`|pre| + 1` has the same side-run position as `y`, and `γc` is empty or the whole gap of a side `s`
whose successor side `s'` in `L` starts at `y`. -/
def TailSplitAt (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (L : List ℕ) (y : ℕ) : Prop :=
  ∃ (u : S.diagram.toCombMap.Dart) (pre γc : List S.diagram.toCombMap.Dart),
    (L.flatMap fun t => P.sideDarts k t ++ Q.gap k t).take y = pre ++ u :: γc ∧
    (L.flatMap (P.sideDarts k))[Q.runPos k L y - 1]? = some u ∧
    Q.runPos k L (pre.length + 1) = Q.runPos k L y ∧
    (γc = [] ∨ ∃ (n s s' : ℕ) (e : S.diagram.toCombMap.Dart),
      (L.flatMap fun t => P.sideDarts k t ++ Q.gap k t)[y]? = some e ∧ γc = Q.gap k s ∧
      L[n]? = some s ∧ L[n + 1]? = some s' ∧ (P.sideDarts k s).getLast? = some u ∧
      (P.sideDarts k s').head? = some e)

/-- Case (a): the position `y` lies inside the first side, at a positive side-run position. -/
theorem tailSplitAt_first (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (s : ℕ)
    (L : List ℕ) (y : ℕ) (hy : y ≤ (P.sideDarts k s).length)
    (hpos : 0 < Q.runPos k (s :: L) y) : TailSplitAt Q k (s :: L) y := by
  have e1 : (P.word k s).length = (P.sideDarts k s).length := by
    simp only [OsinLemma94RealizedPolygons.word, Embedded.dartWord, List.length_map]
  have h1' : y ≤ (P.word k s).length := by omega
  have hrp : Q.runPos k (s :: L) y = y := by
    rw [OsinLemma94ClassPolygons.runPos, if_pos h1']
  rw [hrp] at hpos
  unfold TailSplitAt
  rw [hrp, List.flatMap_cons, List.flatMap_cons]
  obtain ⟨t, rfl⟩ : ∃ t, y = t + 1 := ⟨y - 1, by omega⟩
  have htlt : t < (P.sideDarts k s).length := by omega
  obtain ⟨u, hu⟩ : ∃ u, (P.sideDarts k s)[t]? = some u := ⟨_, List.getElem?_eq_getElem htlt⟩
  have hpl : ((P.sideDarts k s).take t).length = t := List.length_take_of_le htlt.le
  refine ⟨u, (P.sideDarts k s).take t, [], ?_, ?_, ?_, Or.inl rfl⟩
  · rw [List.append_assoc, List.take_append_of_le_length hy, List.take_add_one, hu,
      Option.toList_some]
  · rw [Nat.add_sub_cancel, List.getElem?_append_left htlt]
    exact hu
  · rw [hpl, OsinLemma94ClassPolygons.runPos, if_pos h1']

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowTailSplit.tailSplitAt_first

/-- Case (b): the position `y` is the end of the first block `side_s ++ gap_s`. -/
theorem tailSplitAt_end (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (s : ℕ) (L : List ℕ)
    (y : ℕ) (hne : ∀ t ∈ s :: L, P.sideDarts k t ≠ [])
    (hlast : ∀ t ∈ (s :: L).getLast?, Q.gap k t = [])
    (hy : y = (P.sideDarts k s).length + (Q.gap k s).length) : TailSplitAt Q k (s :: L) y := by
  have e1 : (P.word k s).length = (P.sideDarts k s).length := by
    simp only [OsinLemma94RealizedPolygons.word, Embedded.dartWord, List.length_map]
  have e2 : (Embedded.dartWord S.diagram (Q.gap k s)).length = (Q.gap k s).length := by
    simp only [Embedded.dartWord, List.length_map]
  have hs0 : 0 < (P.sideDarts k s).length := List.length_pos_iff.mpr (hne s List.mem_cons_self)
  have hrp : Q.runPos k (s :: L) y = (P.sideDarts k s).length := by
    rw [OsinLemma94ClassPolygons.runPos]
    split_ifs <;> omega
  obtain ⟨t, ht⟩ : ∃ t, (P.sideDarts k s).length = t + 1 := ⟨(P.sideDarts k s).length - 1, by omega⟩
  have htlt : t < (P.sideDarts k s).length := by omega
  obtain ⟨u, hu⟩ : ∃ u, (P.sideDarts k s)[t]? = some u := ⟨_, List.getElem?_eq_getElem htlt⟩
  have hsd : (P.sideDarts k s).take t ++ [u] = P.sideDarts k s := by
    have h := List.take_add_one (l := P.sideDarts k s) (i := t)
    rw [hu, Option.toList_some, ← ht, List.take_length] at h
    exact h.symm
  have hblock : P.sideDarts k s ++ Q.gap k s = (P.sideDarts k s).take t ++ u :: Q.gap k s := by
    rw [← List.singleton_append, ← List.append_assoc, hsd]
  have hlen2 : (P.sideDarts k s ++ Q.gap k s).length = y := by
    rw [List.length_append]
    omega
  unfold TailSplitAt
  rw [hrp, List.flatMap_cons, List.flatMap_cons]
  refine ⟨u, (P.sideDarts k s).take t, Q.gap k s, ?_, ?_, ?_, ?_⟩
  · rw [List.take_left' hlen2]
    exact hblock
  · rw [ht, Nat.add_sub_cancel, List.getElem?_append_left htlt]
    exact hu
  · have hpl : ((P.sideDarts k s).take t).length = t := List.length_take_of_le htlt.le
    have hc : t + 1 ≤ (P.word k s).length := by omega
    rw [hpl, OsinLemma94ClassPolygons.runPos, if_pos hc]
    exact ht.symm
  · by_cases hg : Q.gap k s = []
    · exact Or.inl hg
    · right
      cases L with
      | nil =>
        exact absurd (hlast s (Option.mem_def.mpr (by rw [List.getLast?_singleton]))) hg
      | cons s' L' =>
        have hs' : 0 < (P.sideDarts k s').length :=
          List.length_pos_iff.mpr (hne s' (List.mem_cons_of_mem s List.mem_cons_self))
        obtain ⟨e, he⟩ : ∃ e, (P.sideDarts k s')[0]? = some e :=
          ⟨_, List.getElem?_eq_getElem hs'⟩
        have hl1 : (P.sideDarts k s ++ Q.gap k s).length ≤ y := by omega
        have hy0 : y - (P.sideDarts k s ++ Q.gap k s).length = 0 := by omega
        refine ⟨0, s, s', e, ?_, rfl, rfl, rfl, ?_, ?_⟩
        · rw [List.getElem?_append_right hl1, hy0, List.flatMap_cons, List.append_assoc,
            List.getElem?_append_left hs']
          exact he
        · rw [List.getLast?_eq_getElem?, ht, Nat.add_sub_cancel]
          exact hu
        · rw [List.head?_eq_getElem?]
          exact he

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowTailSplit.tailSplitAt_end

end Block

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.WindowTailSplit
