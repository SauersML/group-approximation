import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.StepPair
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: the different-kind branch

Take a backwards class-word pair `C` with no endpoint strictly inside a gap, whose classes have
different kinds and whose target is not a cutting path.

1. `a` is inside no gap and before the end of its class word. So it has the vertex of a position
   `x₀` with `[x₀, x₀ + 1]` inside a side `s` of the source class (`exists_forward_side`).
2. `b` is inside no gap and positive. So it has the vertex of a position `y₀` with `[y₀ - 1, y₀]`
   inside a side `t` of the target class (`exists_backward_side`).
3. The start distance `d(v(y₀), v(x₀))` is `d(v(b), v(a)) = |C.startConnector| < ε`.
4. By the triangle inequality, with one-letter steps,
   `d(v(x₀ + 1), v(y₀ - 1)) ≤ 1 + d(v(x₀), v(y₀)) + 1 = |C.startConnector| + 2`.
5. `false_of_sideSteps` refutes the step pair once `|C.startConnector| + 2 < ε`.

## The flagged spot

`startConnector_margin` claims `|C.startConnector| + 2 < ε` from `|C.startConnector| < ε`. That is
false in general, and it is the exact remaining gap of this branch: the split at a gap vertex
needs a connector with two letters to spare.

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

/-- **The different-kind branch, with two letters to spare** on the start connector. -/
theorem false_of_diffKind_margin (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps)
    (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hback : C.b' < C.b) (hnogap : ¬ Q.GapEndpoint k C)
    (hcut : Q.classKind k C.target ≠ .cutting)
    (hkind : Q.classKind k C.source ≠ Q.classKind k C.target)
    (hmargin : C.startConnector.length + 2 < eps) : False := by
  have hngA : ¬ Q.InGap k C.source C.a := fun h => hnogap (Or.inl h)
  have hngB : ¬ Q.InGap k C.target C.b := fun h => hnogap (Or.inr (Or.inr (Or.inl h)))
  have hfwd := C.source_forward
  have ha' := C.a'_le
  have hbl := C.b_le
  obtain ⟨s, off, x0, hs, hx0, hx0', ex⟩ := exists_forward_side Q C.source_lt (by omega) hngA
  obtain ⟨t, off', y0, ht, hy0, hy0', ey⟩ :=
    exists_backward_side Q C.target_lt (by omega) hbl hngB
  have hendS := sideAt_end_le Q hs
  have hendT := sideAt_end_le Q ht
  have hS := (symmetricLabelAlphabet D).alphabet.symmetricGenerating
  have hd : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) y0)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) x0) =
        C.startConnector.length := by
    rw [ex, ey, C.start_geodesic.2.2]
  have e1 := OsinLemma94ClassPolygons.wordDist_vertex_le_of_near C.source_admissible
    (Q.corner k C.source) (x := x0 + 1) (y := x0) (d := 1) (by omega) (by omega) (by omega)
    (by omega)
  have e2 := wordDist_triangle hS
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) (x0 + 1))
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) x0)
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) y0)
  have e3 := OsinLemma94ClassPolygons.wordDist_vertex_le_of_near C.target_admissible
    (Q.corner k C.target) (x := y0) (y := y0 - 1) (d := 1) (by omega) (by omega) (by omega)
    (by omega)
  have e4 := wordDist_triangle hS
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) (x0 + 1))
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) y0)
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) (y0 - 1))
  have e5 := wordDist_comm hS
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) x0)
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) y0)
  exact false_of_sideSteps Q heps C.source_lt C.target_lt C.distinct C.source_mem C.target_mem
    C.source_admissible C.target_admissible hcut hkind hs ht hx0 (by omega) hy0 hy0'
    (by rw [hd]; exact C.start_short) (by omega)

/-- **The margin on the start connector (flagged).**  The split of case 3 needs two letters to
spare; the connector pair only gives `|C.startConnector| < ε`.  This is the remaining gap of the
different-kind branch. -/
theorem startConnector_margin (Q : OsinLemma94ClassPolygons P) {k : Fin P.count}
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps) :
    C.startConnector.length + 2 < eps := by
  have hshort := C.start_short
  omega

/-- **The different-kind branch** of the gap-spanning case. -/
theorem false_of_diffKind (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hback : C.b' < C.b) (hnogap : ¬ Q.GapEndpoint k C)
    (hcut : Q.classKind k C.target ≠ .cutting)
    (hkind : Q.classKind k C.source ≠ Q.classKind k C.target) : False :=
  false_of_diffKind_margin Q heps k C hback hnogap hcut hkind
    (startConnector_margin Q C)

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_diffKind_margin
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_diffKind
