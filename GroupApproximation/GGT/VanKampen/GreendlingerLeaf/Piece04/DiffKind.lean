import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.StepPair
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: the different-kind branch

Take a backwards class-word pair `C` with no endpoint strictly inside a gap, whose classes have
different kinds and whose target is not a cutting path.  Write `v` for the vertices of the class
words, `d` for the word metric, and `len_s`, `len_t` for the lengths of the source and target class
words.

1. The start pair `(a, b)` has `d(v(b), v(a)) = |C.startConnector| < ε`, and the end pair `(a', b')`
   has `d(v(b'), v(a')) = |C.endConnector| < ε`.
2. Every position `x < len` inside no gap has the vertex of a position `x₀` with `[x₀, x₀ + 1]`
   inside a side word (`exists_forward_side`). Every position `0 < y` inside no gap has the vertex
   of a position `y₀` with `[y₀ - 1, y₀]` inside a side word (`exists_backward_side`).
3. Move a pair `(x, y)` with `d(v(y), v(x)) = δ` to a step pair `[x₁, x₁ + 1]`, `[y₁, y₁ + 1]` inside
   sides. One-letter moves change distances by at most one (`wordDist_move_le`), so the step
   distances `d(v(y₁ + 1), v(x₁))` and `d(v(y₁), v(x₁ + 1))` are bounded as follows.
   * Both moved forward (`false_of_forwardPair`), with `x₁ = x₀` and `y₁ = y₀`: `δ + 1` and `δ + 1`.
   * Both moved backward (`false_of_backwardPair`), with `x₁ + 1 = x₀` and `y₁ + 1 = y₀`: `δ + 1`
     and `δ + 1`.
   * Source forward, target backward (`false_of_forwardBackwardPair`): `δ` and `δ + 2`.
   * Source backward, target forward (`false_of_backwardForwardPair`): `δ + 2` and `δ`.
   With `δ < ε`, the first two cases give distances at most `ε`. The mixed cases need `δ + 2 ≤ ε`.
   `false_of_sideSteps` then refutes the step pair.
4. The dispatch (`false_of_diffKind`) goes as follows.
   * If `b < len_t`, move the start pair forward.
   * If `0 < a`, move it backward (`0 < b`, since `b' < b`).
   * If `a' < len_s`, move the end pair forward.
   * If `0 < b'`, move it backward.
   * Otherwise the pair is full-word: `a = 0`, `a' = len_s`, `b' = 0`, `b = len_t`. The start pair is
     mixed, and it is refuted if `|C.startConnector| + 2 ≤ ε`. The end pair is mixed, and it is
     refuted if `|C.endConnector| + 2 ≤ ε`.
   * What remains is a full-word pair with both connectors of length `ε - 1`. This is taken as the
     hypothesis `hfull` (the residual `ClassFullWordDiffKindStatement` of `Piece04.Gap`).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.WordMetric
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **Moving the endpoints of a cross distance.**  Moving the position on class `i` by at most `dx`
letters and the position on class `i'` by at most `dy` letters changes their distance by at most
`dy + dx`. -/
theorem wordDist_move_le (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i i' x x' y y' dx dy : ℕ}
    (hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i))
    (hadm' : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i'))
    (hx : x ≤ (Q.word k i).length) (hx' : x' ≤ (Q.word k i).length)
    (hxx : x ≤ x' + dx) (hxx' : x' ≤ x + dx)
    (hy : y ≤ (Q.word k i').length) (hy' : y' ≤ (Q.word k i').length)
    (hyy : y ≤ y' + dy) (hyy' : y' ≤ y + dy) :
    wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (OsinComponents.vertex (Q.corner k i') (Q.word k i') y')
        (OsinComponents.vertex (Q.corner k i) (Q.word k i) x') ≤
      wordDist (symmetricLabelAlphabet D).alphabet.carrier
          (OsinComponents.vertex (Q.corner k i') (Q.word k i') y)
          (OsinComponents.vertex (Q.corner k i) (Q.word k i) x) + dy + dx := by
  have hS := (symmetricLabelAlphabet D).alphabet.symmetricGenerating
  have e1 := OsinLemma94ClassPolygons.wordDist_vertex_le_of_near hadm' (Q.corner k i')
    (x := y') (y := y) (d := dy) hy' hy hyy' hyy
  have e2 := OsinLemma94ClassPolygons.wordDist_vertex_le_of_near hadm (Q.corner k i)
    (x := x) (y := x') (d := dx) hx hx' hxx hxx'
  have e3 := wordDist_triangle hS
    (OsinComponents.vertex (Q.corner k i') (Q.word k i') y')
    (OsinComponents.vertex (Q.corner k i') (Q.word k i') y)
    (OsinComponents.vertex (Q.corner k i) (Q.word k i) x')
  have e4 := wordDist_triangle hS
    (OsinComponents.vertex (Q.corner k i') (Q.word k i') y)
    (OsinComponents.vertex (Q.corner k i) (Q.word k i) x)
    (OsinComponents.vertex (Q.corner k i) (Q.word k i) x')
  omega

/-- **A pair of positions moved forward.**  Positions `x` of an (A1) class and `y` of a long class of
a different, non-cutting kind, both before the end of their words and inside no gap, with
`d(v(y), v(x)) < ε`, give a contradiction once `ε ≥ 3`. -/
theorem false_of_forwardPair (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps) {k : Fin P.count}
    {i i' x y : ℕ} (hi : i < Q.classCount k) (hi' : i' < Q.classCount k)
    (hii' : i ≠ i') (hrel : i ∈ Q.relatorClasses k) (hlong : i' ∈ Q.longClasses k)
    (hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i))
    (hadm' : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i'))
    (hcut : Q.classKind k i' ≠ .cutting) (hkind : Q.classKind k i ≠ Q.classKind k i')
    (hx : x < (Q.word k i).length) (hngx : ¬ Q.InGap k i x)
    (hy : y < (Q.word k i').length) (hngy : ¬ Q.InGap k i' y)
    (hd : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k i') (Q.word k i') y)
      (OsinComponents.vertex (Q.corner k i) (Q.word k i) x) < eps) : False := by
  obtain ⟨s, off, x0, hs, hx0, hx0', ex⟩ := exists_forward_side Q hi hx hngx
  obtain ⟨t, off', y0, ht, hy0, hy0', ey⟩ := exists_forward_side Q hi' hy hngy
  have hendS := sideAt_end_le Q hs
  have hendT := sideAt_end_le Q ht
  rw [← ex, ← ey] at hd
  have hstart := wordDist_move_le Q hadm hadm' (x := x0) (x' := x0) (y := y0) (y' := y0 + 1)
    (dx := 0) (dy := 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have hend := wordDist_move_le Q hadm hadm' (x := x0) (x' := x0 + 1) (y := y0) (y' := y0)
    (dx := 1) (dy := 0) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  exact false_of_sideSteps Q heps hi hi' hii' hrel hlong hadm hadm' hcut hkind hs ht hx0
    (by omega) hy0 (by omega) (by omega) (by omega)

/-- **A pair of positions moved backward.**  As `false_of_forwardPair`, for positive positions. -/
theorem false_of_backwardPair (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps)
    {k : Fin P.count} {i i' x y : ℕ} (hi : i < Q.classCount k) (hi' : i' < Q.classCount k)
    (hii' : i ≠ i') (hrel : i ∈ Q.relatorClasses k) (hlong : i' ∈ Q.longClasses k)
    (hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i))
    (hadm' : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i'))
    (hcut : Q.classKind k i' ≠ .cutting) (hkind : Q.classKind k i ≠ Q.classKind k i')
    (hx0 : 0 < x) (hx : x ≤ (Q.word k i).length) (hngx : ¬ Q.InGap k i x)
    (hy0 : 0 < y) (hy : y ≤ (Q.word k i').length) (hngy : ¬ Q.InGap k i' y)
    (hd : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k i') (Q.word k i') y)
      (OsinComponents.vertex (Q.corner k i) (Q.word k i) x) < eps) : False := by
  obtain ⟨s, off, x1, hs, hx1, hx1', ex⟩ := exists_backward_side Q hi hx0 hx hngx
  obtain ⟨t, off', y1, ht, hy1, hy1', ey⟩ := exists_backward_side Q hi' hy0 hy hngy
  have hendS := sideAt_end_le Q hs
  have hendT := sideAt_end_le Q ht
  rw [← ex, ← ey] at hd
  obtain ⟨x0, rfl⟩ : ∃ x0, x1 = x0 + 1 := ⟨x1 - 1, by omega⟩
  obtain ⟨y0, rfl⟩ : ∃ y0, y1 = y0 + 1 := ⟨y1 - 1, by omega⟩
  have hstart := wordDist_move_le Q hadm hadm' (x := x0 + 1) (x' := x0) (y := y0 + 1)
    (y' := y0 + 1) (dx := 1) (dy := 0) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hend := wordDist_move_le Q hadm hadm' (x := x0 + 1) (x' := x0 + 1) (y := y0 + 1)
    (y' := y0) (dx := 0) (dy := 1) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  exact false_of_sideSteps (x := x0) (y := y0) Q heps hi hi' hii' hrel hlong hadm hadm' hcut
    hkind hs ht (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **A pair of positions, the source moved forward and the target backward.**  As
`false_of_forwardPair`, with `d(v(y), v(x)) + 2 ≤ ε`. -/
theorem false_of_forwardBackwardPair (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps)
    {k : Fin P.count} {i i' x y : ℕ} (hi : i < Q.classCount k) (hi' : i' < Q.classCount k)
    (hii' : i ≠ i') (hrel : i ∈ Q.relatorClasses k) (hlong : i' ∈ Q.longClasses k)
    (hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i))
    (hadm' : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i'))
    (hcut : Q.classKind k i' ≠ .cutting) (hkind : Q.classKind k i ≠ Q.classKind k i')
    (hx : x < (Q.word k i).length) (hngx : ¬ Q.InGap k i x)
    (hy0 : 0 < y) (hy : y ≤ (Q.word k i').length) (hngy : ¬ Q.InGap k i' y)
    (hd : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k i') (Q.word k i') y)
      (OsinComponents.vertex (Q.corner k i) (Q.word k i) x) + 2 ≤ eps) : False := by
  obtain ⟨s, off, x0, hs, hx0, hx0', ex⟩ := exists_forward_side Q hi hx hngx
  obtain ⟨t, off', y1, ht, hy1, hy1', ey⟩ := exists_backward_side Q hi' hy0 hy hngy
  have hendS := sideAt_end_le Q hs
  have hendT := sideAt_end_le Q ht
  rw [← ex, ← ey] at hd
  obtain ⟨y0, rfl⟩ : ∃ y0, y1 = y0 + 1 := ⟨y1 - 1, by omega⟩
  have hend := wordDist_move_le Q hadm hadm' (x := x0) (x' := x0 + 1) (y := y0 + 1) (y' := y0)
    (dx := 1) (dy := 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  exact false_of_sideSteps Q heps hi hi' hii' hrel hlong hadm hadm' hcut hkind hs ht hx0
    (by omega) (y := y0) (by omega) (by omega) (by omega) (by omega)

/-- **A pair of positions, the source moved backward and the target forward.**  As
`false_of_forwardPair`, with `d(v(y), v(x)) + 2 ≤ ε`. -/
theorem false_of_backwardForwardPair (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps)
    {k : Fin P.count} {i i' x y : ℕ} (hi : i < Q.classCount k) (hi' : i' < Q.classCount k)
    (hii' : i ≠ i') (hrel : i ∈ Q.relatorClasses k) (hlong : i' ∈ Q.longClasses k)
    (hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i))
    (hadm' : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i'))
    (hcut : Q.classKind k i' ≠ .cutting) (hkind : Q.classKind k i ≠ Q.classKind k i')
    (hx0 : 0 < x) (hx : x ≤ (Q.word k i).length) (hngx : ¬ Q.InGap k i x)
    (hy : y < (Q.word k i').length) (hngy : ¬ Q.InGap k i' y)
    (hd : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k i') (Q.word k i') y)
      (OsinComponents.vertex (Q.corner k i) (Q.word k i) x) + 2 ≤ eps) : False := by
  obtain ⟨s, off, x1, hs, hx1, hx1', ex⟩ := exists_backward_side Q hi hx0 hx hngx
  obtain ⟨t, off', y0, ht, hy0, hy0', ey⟩ := exists_forward_side Q hi' hy hngy
  have hendS := sideAt_end_le Q hs
  have hendT := sideAt_end_le Q ht
  rw [← ex, ← ey] at hd
  obtain ⟨x0, rfl⟩ : ∃ x0, x1 = x0 + 1 := ⟨x1 - 1, by omega⟩
  have hstart := wordDist_move_le Q hadm hadm' (x := x0 + 1) (x' := x0) (y := y0) (y' := y0 + 1)
    (dx := 1) (dy := 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  exact false_of_sideSteps (x := x0) Q heps hi hi' hii' hrel hlong hadm hadm' hcut hkind hs ht
    (by omega) (by omega) hy0 (by omega) (by omega) (by omega)

/-- The start distance of a class-word pair is the length of its start connector. -/
theorem wordDist_start_eq (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps) :
    wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
        (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a) =
      C.startConnector.length :=
  C.start_geodesic.2.2.symm

/-- The end distance of a class-word pair, from target to source, is the length of its end
connector. -/
theorem wordDist_end_eq (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps) :
    wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b')
        (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a') =
      C.endConnector.length := by
  rw [wordDist_comm (symmetricLabelAlphabet D).alphabet.symmetricGenerating]
  exact C.end_geodesic.2.2.symm

/-- **The different-kind branch** of the gap-spanning case, but for full-word pairs with both
connectors of length `ε - 1`, which are taken as the hypothesis `hfull`. -/
theorem false_of_diffKind (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hback : C.b' < C.b) (hnogap : ¬ Q.GapEndpoint k C)
    (hcut : Q.classKind k C.target ≠ .cutting)
    (hkind : Q.classKind k C.source ≠ Q.classKind k C.target)
    (hfull : C.a = 0 → C.a' = (Q.word k C.source).length → C.b' = 0 →
      C.b = (Q.word k C.target).length → C.startConnector.length + 1 = eps →
      C.endConnector.length + 1 = eps → False) : False := by
  have hngA : ¬ Q.InGap k C.source C.a := fun h => hnogap (Or.inl h)
  have hngA' : ¬ Q.InGap k C.source C.a' := fun h => hnogap (Or.inr (Or.inl h))
  have hngB : ¬ Q.InGap k C.target C.b := fun h => hnogap (Or.inr (Or.inr (Or.inl h)))
  have hngB' : ¬ Q.InGap k C.target C.b' := fun h => hnogap (Or.inr (Or.inr (Or.inr h)))
  have hst := wordDist_start_eq Q C
  have hen := wordDist_end_eq Q C
  have hs := C.start_short
  have he := C.end_short
  have hfwd := C.source_forward
  have ha' := C.a'_le
  have hbl := C.b_le
  by_cases h1 : C.b < (Q.word k C.target).length
  · exact false_of_forwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
      C.target_mem C.source_admissible C.target_admissible hcut hkind (by omega) hngA h1 hngB
      (by omega)
  by_cases h2 : 0 < C.a
  · exact false_of_backwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
      C.target_mem C.source_admissible C.target_admissible hcut hkind h2 C.a_le hngA (by omega)
      hbl hngB (by omega)
  by_cases h3 : C.a' < (Q.word k C.source).length
  · exact false_of_forwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
      C.target_mem C.source_admissible C.target_admissible hcut hkind h3 hngA' (by omega) hngB'
      (by omega)
  by_cases h4 : 0 < C.b'
  · exact false_of_backwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
      C.target_mem C.source_admissible C.target_admissible hcut hkind (by omega) ha' hngA' h4
      C.b'_le hngB' (by omega)
  by_cases h5 : C.startConnector.length + 2 ≤ eps
  · exact false_of_forwardBackwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
      C.target_mem C.source_admissible C.target_admissible hcut hkind (by omega) hngA (by omega)
      hbl hngB (by omega)
  by_cases h6 : C.endConnector.length + 2 ≤ eps
  · exact false_of_backwardForwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
      C.target_mem C.source_admissible C.target_admissible hcut hkind (by omega) ha' hngA'
      (by omega) hngB' (by omega)
  exact hfull (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.wordDist_move_le
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_forwardPair
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_backwardPair
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_forwardBackwardPair
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_backwardForwardPair
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.wordDist_start_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.wordDist_end_eq
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_diffKind
