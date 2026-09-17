import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassGapSpanModel
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCornerMove
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkHolds
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: the side cover of a class word

Target: `OsinLemma94ClassCaseGapSpanStatement` (module `OsinLemma94ClassPairShapes`). Take a
backwards connector pair `C` on the class words of `Q : OsinLemma94ClassPolygons P` that is not
single-side and has no endpoint strictly inside a gap.

## The proof

The eps threshold is `max 3 (max eps₁ eps₂)`: `eps₁` is the Morse threshold
`2κ + c ≤ λ ε` (`exists_morse_threshold_of_fourPoint`), and `eps₂` comes from the relator-cell
branch. The `ρ` threshold is the one of the relator-cell branch. There are three cases.

1. **Cutting target class.** `osinLemma94ClassCaseTwo_false` applies, since it needs no
   single-side hypothesis.
2. **Equal kinds.** The windows are reversed arcs `p` and `q` of one relator cell `j`, and the face
   walk reads `X T Y S` (`OsinLemma94ClassPolygons.exists_sameCellWalk`).
   * If a rotation `q B p A` of the cell has `X B = 1` or `Y A = 1`, the value-one kills
     `false_of_classSameCell_value_one_X` and `_Y` refute the pair.
   * Otherwise we are in `OsinLemma94ClassCaseOneRCellStatement` (module `Piece04.RCell`).
3. **Different kinds, non-cutting target** (module `Piece04.DiffKind`).
   * Every position of a class word that is not inside a gap has the same vertex as a position
     inside a side word (this module).
     * `exists_forward_side`: moving forward, a position at the start of a gap moves to the start
       of the next side. The gap has value one (`vertex_gap_end_eq`), and sides are nonempty.
     * `exists_backward_side`: moving backward, a position at the end of a gap moves to the end of
       its side.
   * So `a` has the vertex of `x₀` with `[x₀, x₀ + 1]` inside a side `s` of the source class, and
     `b` has the vertex of `y₀` with `[y₀ - 1, y₀]` inside a side `t` of the target class.
   * The side-level short pair `(s, [x₀, x₀+1]; t, [y₀-1, y₀])` (`false_of_sideSteps`, module
     `Piece04.StepPair`) is backwards. Its sides have the kinds of their classes, so the kinds
     differ and the target is not cutting. `osinLemma94ShortCaseOne_false` refutes it once both
     connectors are shorter than `ε`.
   * The start connector has length `d = |C.startConnector| < ε`, because the vertices are those of
     `C`. The end connector has length at most `d + 2` by the triangle inequality.

## The remaining mathematical gap

The step pair of case 3 needs `d + 2 < ε`, while `C` only gives `d < ε`. That is
`startConnector_margin` in `Piece04.DiffKind`, the one flagged spot of that branch.

Splitting a spanning pair at a gap vertex needs a connector of length `< ε` from that vertex. The
hyperbolic thinness of the quadrilateral bounds it only by `ε` plus a constant, as the docstring
of `OsinLemma94ClassGapSpanModel` notes. The side-level short Case 1 is stated at the same `ε` as
the section family, so there is no room.

Case 2 needs the class analogue of the enclosed-subdiagram argument behind
`osinLemma94CaseOneSameCell`. The flagged spot is `singleSidePair_of_noGap` in `Piece04.RCell`,
which states exactly the failing claim: a pair with no gap endpoint does not span a gap.

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **The block of a flat map containing a position.** -/
theorem exists_block_of_lt_length {α β : Type*} (f : α → List β) :
    ∀ (L : List α) (x : ℕ), x < (L.flatMap f).length →
      ∃ (L1 : List α) (s : α) (L2 : List α), L = L1 ++ s :: L2 ∧
        (L1.flatMap f).length ≤ x ∧ x < (L1.flatMap f).length + (f s).length := by
  intro L
  induction L with
  | nil =>
    intro x hx
    simp at hx
  | cons s L ih =>
    intro x hx
    rw [List.flatMap_cons, List.length_append] at hx
    by_cases hlt : x < (f s).length
    · exact ⟨[], s, L, rfl, by simp, by simpa using hlt⟩
    · obtain ⟨L1, s', L2, hL, h1, h2⟩ := ih (x - (f s).length) (by omega)
      refine ⟨s :: L1, s', L2, by rw [hL, List.cons_append], ?_, ?_⟩
      · rw [List.flatMap_cons, List.length_append]
        omega
      · rw [List.flatMap_cons, List.length_append]
        omega

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **Every position of a class word lies in the block of one side**, its word with its gap. -/
theorem exists_sideAt_block (Q : OsinLemma94ClassPolygons P) (k : Fin P.count) (i : ℕ) {x : ℕ}
    (hx : x < (Q.word k i).length) :
    ∃ s off, Q.SideAt k i s off ∧ off ≤ x ∧
      x < off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length := by
  rw [Q.word_eq] at hx
  obtain ⟨L1, s, L2, hL, h1, h2⟩ := exists_block_of_lt_length
    (fun t => P.word k t ++ Embedded.dartWord S.diagram (Q.gap k t)) (Q.classSides k i) x hx
  refine ⟨s, (L1.flatMap fun t => P.word k t ++ Embedded.dartWord S.diagram (Q.gap k t)).length,
    ⟨L1, L2, hL, rfl⟩, h1, ?_⟩
  simp only [List.length_append] at h2
  omega

/-- The block of a side ends inside the class word. -/
theorem sideAt_end_le (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s off : ℕ}
    (h : Q.SideAt k i s off) :
    off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length ≤
      (Q.word k i).length := by
  obtain ⟨A, R, hw, hA⟩ := h.word_split
  rw [hw]
  simp only [List.length_append]
  omega

/-- **A nonempty gap is followed by a side.**  The last side of a class has no gap. -/
theorem exists_next_sideAt (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s off : ℕ}
    (hi : i < Q.classCount k) (h : Q.SideAt k i s off)
    (hgap : 0 < (Embedded.dartWord S.diagram (Q.gap k s)).length) :
    ∃ s', Q.SideAt k i s'
      (off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) := by
  obtain ⟨L1, L2, hL, hoff⟩ := h
  cases L2 with
  | nil =>
    have hlast : s ∈ (Q.classSides k i).getLast? :=
      Option.mem_def.mpr (by rw [hL, List.getLast?_concat])
    have hg := Q.gap_last k i hi s hlast
    rw [hg] at hgap
    simp [Embedded.dartWord] at hgap
  | cons s' L3 =>
    refine ⟨s', L1 ++ [s], L3, by rw [hL]; simp, ?_⟩
    simp only [List.flatMap_append, List.flatMap_singleton, List.length_append]
    omega

/-- A side of a class has a nonempty word. -/
theorem word_length_pos_of_sideAt (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    {i s off : ℕ} (hi : i < Q.classCount k) (h : Q.SideAt k i s off) :
    0 < (P.word k s).length := by
  have hlt : s < P.sideCount k := Q.lt_sideCount_of_mem k i hi s (Q.mem_of_sideAt h)
  rw [CaseOneWalk.polygon_length_word]
  exact List.length_pos_iff.mpr (P.side_ne_nil k s hlt)

/-- **Forward to a side.**  A position of a class word inside no gap, before the end of the word, has
the vertex of a position `x₀` of the same class word with `[x₀, x₀ + 1]` inside the word of a side. -/
theorem exists_forward_side (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i x : ℕ}
    (hi : i < Q.classCount k) (hx : x < (Q.word k i).length) (hng : ¬ Q.InGap k i x) :
    ∃ s off x0, Q.SideAt k i s off ∧ off ≤ x0 ∧ x0 < off + (P.word k s).length ∧
      OsinComponents.vertex (Q.corner k i) (Q.word k i) x0 =
        OsinComponents.vertex (Q.corner k i) (Q.word k i) x := by
  obtain ⟨s, off, hs, h1, h2⟩ := exists_sideAt_block Q k i hx
  by_cases hin : x < off + (P.word k s).length
  · exact ⟨s, off, x, hs, h1, hin, rfl⟩
  · have hx' : x = off + (P.word k s).length := by
      by_contra hne
      exact hng ⟨s, off, hs, by omega, h2⟩
    obtain ⟨s', hs'⟩ := exists_next_sideAt Q hi hs (by omega)
    have hpos := word_length_pos_of_sideAt Q hi hs'
    refine ⟨s', off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length,
      off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length, hs',
      le_refl _, by omega, ?_⟩
    rw [Q.vertex_gap_end_eq hi hs, hx']

/-- **Backward to a side.**  A positive position of a class word inside no gap has the vertex of a
position `y₀` of the same class word with `[y₀ - 1, y₀]` inside the word of a side. -/
theorem exists_backward_side (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i y : ℕ}
    (hi : i < Q.classCount k) (hy0 : 0 < y) (hy : y ≤ (Q.word k i).length)
    (hng : ¬ Q.InGap k i y) :
    ∃ t off y0, Q.SideAt k i t off ∧ off + 1 ≤ y0 ∧ y0 ≤ off + (P.word k t).length ∧
      OsinComponents.vertex (Q.corner k i) (Q.word k i) y0 =
        OsinComponents.vertex (Q.corner k i) (Q.word k i) y := by
  obtain ⟨t, off, ht, h1, h2⟩ := exists_sideAt_block Q k i (x := y - 1) (by omega)
  by_cases hin : y ≤ off + (P.word k t).length
  · exact ⟨t, off, y, ht, by omega, hin, rfl⟩
  · have hy' : y =
        off + (P.word k t).length + (Embedded.dartWord S.diagram (Q.gap k t)).length := by
      by_contra hne
      exact hng ⟨t, off, ht, by omega, by omega⟩
    have hpos := word_length_pos_of_sideAt Q hi ht
    refine ⟨t, off, off + (P.word k t).length, ht, by omega, le_refl _, ?_⟩
    rw [hy', Q.vertex_gap_end_eq hi ht]

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.exists_forward_side
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.exists_backward_side
