import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94SameCellPocketSides
import GroupApproximation.Meta.AxiomGuard

/-!
# Piece 04, window shapes: where a class dart sits

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, on class words.  Lane `gl-p04-11` proves that two
distinct classes of one relator cell have no common class dart (module
`Piece04.WindowShape.ClassDisjoint`).  This module holds the two position facts it uses.

* `faceOf_of_mem_sideDarts`: a side dart lies on the polygon face `P.face k`, because the walk of
  that face, rotated by `P.base k`, is the concatenation of the sides (`P.walk`).
* `mem_side_of_getElem?_of_length_le`: the last class dart is a side dart.  A class ends with a
  side (`gap_last`), and sides are nonempty (`side_ne_nil`).
* `side_or_gap_succ`: a class dart at position `n` is a side dart of the class, or it is a gap dart
  of the class and position `n + 1` still exists.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- A dart of side `s` of polygon `k` lies on the polygon face. -/
theorem faceOf_of_mem_sideDarts {k : Fin P.count} {s : ℕ} (hs : s < P.sideCount k)
    {x : S.diagram.toCombMap.Dart} (hx : x ∈ P.sideDarts k s) :
    S.diagram.toCombMap.faceOf x = P.face k :=
  SameCellPocketSides.faceOf_of_mem_rotate (P.walk k)
    (List.mem_flatMap.mpr ⟨s, List.mem_range.mpr hs, hx⟩)

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint.faceOf_of_mem_sideDarts

/-- **The last class dart is a side dart.**  Write the sides of class `i` as `ys ++ [sl]`.  The gap
after the last side `sl` is empty (`gap_last`) and side `sl` is nonempty (`side_ne_nil`), so the
class darts end with the darts of side `sl`. -/
theorem mem_side_of_getElem?_of_length_le (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    {i : ℕ} (hi : i < Q.classCount k) {n : ℕ} {x : S.diagram.toCombMap.Dart}
    (hx : (Q.classDarts k i)[n]? = some x) (hlen : (Q.classDarts k i).length ≤ n + 1) :
    ∃ s ∈ Q.classSides k i, x ∈ P.sideDarts k s := by
  obtain ⟨hn, -⟩ := List.getElem?_eq_some_iff.mp hx
  obtain ⟨sl, hsl⟩ : ∃ sl, (Q.classSides k i).getLast? = some sl :=
    ⟨_, List.getLast?_eq_getLast (Q.classSides_ne_nil k i hi)⟩
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hsl
  have hslmem : sl ∈ Q.classSides k i := List.mem_of_getLast? hsl
  have hgap : Q.gap k sl = [] := Q.gap_last k i hi sl (Option.mem_def.mpr hsl)
  have hside : P.sideDarts k sl ≠ [] :=
    P.side_ne_nil k sl (Q.lt_sideCount_of_mem k i hi sl hslmem)
  have hdarts : Q.classDarts k i =
      (ys.flatMap fun s => P.sideDarts k s ++ Q.gap k s) ++ P.sideDarts k sl := by
    unfold OsinLemma94ClassPolygons.classDarts
    rw [hys, List.flatMap_append, List.flatMap_singleton, hgap, List.append_nil]
  have hlast : (Q.classDarts k i).getLast? = some x := by
    rw [List.getLast?_eq_getElem?, show (Q.classDarts k i).length - 1 = n by omega]
    exact hx
  rw [hdarts, List.getLast?_append, List.getLast?_eq_getLast hside, Option.some_or] at hlast
  refine ⟨sl, hslmem, ?_⟩
  rw [← Option.some.inj hlast]
  exact List.getLast_mem hside

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint.mem_side_of_getElem?_of_length_le

/-- **Side dart, or gap dart with a successor.**  A class dart at position `n` lies on a side of
the class, or it lies in the gap after a side of the class and is not the last class dart. -/
theorem side_or_gap_succ (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) {i : ℕ}
    (hi : i < Q.classCount k) {n : ℕ} {x : S.diagram.toCombMap.Dart}
    (hx : (Q.classDarts k i)[n]? = some x) :
    (∃ s ∈ Q.classSides k i, x ∈ P.sideDarts k s) ∨
      ((∃ s ∈ Q.classSides k i, x ∈ Q.gap k s) ∧ n + 1 < (Q.classDarts k i).length) := by
  by_cases hsucc : n + 1 < (Q.classDarts k i).length
  · have hmem : x ∈ (Q.classSides k i).flatMap fun s => P.sideDarts k s ++ Q.gap k s :=
      List.mem_of_getElem? hx
    obtain ⟨s, hs, hxs⟩ := List.mem_flatMap.mp hmem
    rcases List.mem_append.mp hxs with hside | hgap
    · exact Or.inl ⟨s, hs, hside⟩
    · exact Or.inr ⟨⟨s, hs, hgap⟩, hsucc⟩
  · exact Or.inl (mem_side_of_getElem?_of_length_le Q k hi hx (by omega))

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint.side_or_gap_succ

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.WindowShape.ClassDisjoint
