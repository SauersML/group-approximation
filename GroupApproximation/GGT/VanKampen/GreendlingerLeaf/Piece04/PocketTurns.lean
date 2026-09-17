import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.RCellEnclosure
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04: the crossing darts of the class pocket turns

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  This module proves the two
crossing-dart conjuncts of `ClassPocketTurnStatement` (module `Piece04.RCellEnclosure`).  It reduces
that statement to `ClassPocketRotationTurnStatement`, which keeps only the rotation and the first
turns.

## The crossing darts (proved here)

* `mem_classWindow_of_mem_runWindow`: a dart of the run window `runWindow k i x y` lies in the class
  window `classWindow k i x y`.  The side run is the class darts without the gaps.  `runPos` maps a
  class position to its side-run position, and position `t` of the side run sits at a class
  position between `x` and `y` (`getElem?_classDarts_of_sideRun`).
* `runWindow_source_ne_nil`, `runWindow_target_ne_nil`: the run windows are nonempty.  With no
  endpoint inside a gap, the endpoint vertices are prefixes of `classWalk` of lengths given by
  `runPos` (`vertex_eq_classWalk_take`).  An empty window would make the two endpoints equal, and
  the long-segment bound (`source_long`, `target_long`) would read `eps < 0`.
* `exists_source_cross`, `exists_target_cross`: a dart `s` of a run window is a dart of
  `arc.reverseDarts = (arc.darts.reverse).map α`, so `s = α d` for some `d ∈ arc.darts`.

## The isolated statement `ClassPocketRotationTurnStatement` (OPEN)

`∂Π` rotates to `q B p A`, and both complement spellings `B X`, `A Y` are closed by first turns.
This is steps 1, 3 and 4 of the argument in `Piece04.RCellEnclosure`.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.VanKampen.SimpleClosedWalkSides
open GroupApproximation.GGT.VanKampen.CaseOneWalk

/-- An entry of `l` at a position in `[m, n)` lies in the window `(l.drop m).take (n - m)`. -/
theorem mem_window_of_getElem? {α : Type*} {l : List α} {m n i : ℕ} {d : α} (h : l[i]? = some d)
    (hm : m ≤ i) (hn : i < n) : d ∈ (l.drop m).take (n - m) := by
  refine List.mem_iff_getElem?.mpr ⟨i - m, ?_⟩
  rw [List.getElem?_take_of_lt (by omega : i - m < n - m), List.getElem?_drop,
    show m + (i - m) = i by omega]
  exact h

/-- A member of the window `(l.drop m).take k` is an entry of `l` at a position in `[m, m + k)`. -/
theorem exists_getElem?_of_mem_window {α : Type*} {l : List α} {m k : ℕ} {d : α}
    (h : d ∈ (l.drop m).take k) : ∃ i, m ≤ i ∧ i < m + k ∧ l[i]? = some d := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h
  by_cases hjk : j < k
  · rw [List.getElem?_take_of_lt hjk, List.getElem?_drop] at hj
    exact ⟨m + j, by omega, by omega, hj⟩
  · rw [List.getElem?_take, if_neg hjk] at hj
    exact absurd hj (by simp)

/-- A dart reversing a dart of `T` exists on an arc whose reversal contains the nonempty list `T`. -/
theorem exists_cross_of_ne_nil {M : CombMap.{v}} {cycle : List M.Dart} (arc : CyclicArc cycle)
    {T : List M.Dart} (hT : T ≠ []) (hsub : ∀ s ∈ T, s ∈ arc.reverseDarts) :
    ∃ d ∈ arc.darts, M.alpha d ∈ T := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil T hT
  have h := hsub s hs
  simp only [CyclicArc.reverseDarts, List.mem_map, List.mem_reverse] at h
  obtain ⟨d, hd, hds⟩ := h
  exact ⟨d, hd, by rw [hds]; exact hs⟩

section CrossingDarts

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- Position `t` of the side run of the sides `L` is a position `t'` of their class darts, with
`runPos` bounds transported to `t'`. -/
theorem getElem?_classDarts_of_sideRun (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) :
    ∀ (L : List ℕ) (t : ℕ) (d : S.diagram.toCombMap.Dart),
      (L.flatMap (P.sideDarts k))[t]? = some d →
      ∃ t', (L.flatMap fun s => P.sideDarts k s ++ Q.gap k s)[t']? = some d ∧
        (∀ x, Q.runPos k L x ≤ t → x ≤ t') ∧ (∀ y, t < Q.runPos k L y → t' < y)
  | [], t, d, h => by simp at h
  | s :: L, t, d, h => by
    have e1 : (P.word k s).length = (P.sideDarts k s).length := by
      simp only [OsinLemma94RealizedPolygons.word, Embedded.dartWord, List.length_map]
    simp only [List.flatMap_cons] at h
    by_cases ht : t < (P.sideDarts k s).length
    · rw [List.getElem?_append_left ht] at h
      refine ⟨t, ?_, fun x hx => ?_, fun y hy => ?_⟩
      · simp only [List.flatMap_cons, List.append_assoc]
        rw [List.getElem?_append_left ht]
        exact h
      · rw [OsinLemma94ClassPolygons.runPos] at hx
        split_ifs at hx <;> omega
      · rw [OsinLemma94ClassPolygons.runPos] at hy
        split_ifs at hy <;> omega
    · have e2 : (Embedded.dartWord S.diagram (Q.gap k s)).length = (Q.gap k s).length := by
        simp only [Embedded.dartWord, List.length_map]
      have hle : (P.sideDarts k s).length ≤ t := Nat.le_of_not_lt ht
      rw [List.getElem?_append_right hle] at h
      obtain ⟨t'', h'', hx'', hy''⟩ :=
        getElem?_classDarts_of_sideRun Q k L (t - (P.sideDarts k s).length) d h
      refine ⟨(P.sideDarts k s).length + (Q.gap k s).length + t'', ?_, fun x hx => ?_,
        fun y hy => ?_⟩
      · simp only [List.flatMap_cons, List.append_assoc]
        have h1 : (P.sideDarts k s).length ≤
            (P.sideDarts k s).length + (Q.gap k s).length + t'' := by omega
        rw [List.getElem?_append_right h1]
        have h2 : (Q.gap k s).length ≤
            (P.sideDarts k s).length + (Q.gap k s).length + t'' - (P.sideDarts k s).length := by
          omega
        rw [List.getElem?_append_right h2, show (P.sideDarts k s).length + (Q.gap k s).length +
          t'' - (P.sideDarts k s).length - (Q.gap k s).length = t'' by omega]
        exact h''
      · rw [OsinLemma94ClassPolygons.runPos] at hx
        split_ifs at hx
        · omega
        · omega
        · have h3 := hx'' (x - (P.word k s).length -
            (Embedded.dartWord S.diagram (Q.gap k s)).length) (by omega)
          omega
      · rw [OsinLemma94ClassPolygons.runPos] at hy
        split_ifs at hy
        · omega
        · omega
        · have h3 := hy'' (y - (P.word k s).length -
            (Embedded.dartWord S.diagram (Q.gap k s)).length) (by omega)
          omega

/-- A dart of a run window lies in the class window with the same endpoints. -/
theorem mem_classWindow_of_mem_runWindow (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    {i x y : ℕ} (hxy : x ≤ y) {d : S.diagram.toCombMap.Dart} (hd : d ∈ Q.runWindow k i x y) :
    d ∈ Q.classWindow k i x y := by
  have hd' : d ∈ (((Q.classSides k i).flatMap (P.sideDarts k)).drop
      (Q.runPos k (Q.classSides k i) x)).take
      (Q.runPos k (Q.classSides k i) y - Q.runPos k (Q.classSides k i) x) := hd
  show d ∈ (((Q.classSides k i).flatMap fun s => P.sideDarts k s ++ Q.gap k s).drop x).take (y - x)
  have hmono := Q.runPos_mono k (Q.classSides k i) hxy
  obtain ⟨t, ht₁, ht₂, ht⟩ := exists_getElem?_of_mem_window hd'
  obtain ⟨t', ht', hx, hy⟩ := getElem?_classDarts_of_sideRun Q k (Q.classSides k i) t d ht
  exact mem_window_of_getElem? ht' (hx x ht₁) (hy y (by omega))
