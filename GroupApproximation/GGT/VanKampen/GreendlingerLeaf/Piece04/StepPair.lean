import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.SideCover
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.ShortSucc
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: the one-step side pair

Take positions `x` of class `i` and `y` of class `i'` such that `[x, x + 1]` lies inside the word of
side `s` of class `i` and `[y, y + 1]` inside the word of side `t` of class `i'`.

* The vertices of the class words at these positions are the vertices of the side words at the
  shifted positions, up to one common left factor (`OsinLemma94ClassPolygons.vertex_eq_of_sideAt`).
* The word metric is left invariant, so geodesic connectors between the side vertices have the
  lengths of the class distances.
* The side `s` is an (A1) side, because its class is. The side `t` is not short, because its class
  is not. The sides differ, because different classes have disjoint sides. Sides have the kinds of
  their classes (`kind_eq`).
* So `(s, [x - off, x + 1 - off]; t, b = y + 1 - off', b' = y - off')` is a backwards short pair of
  polygon `k` at parameter `ε + 1`, once both class distances are at most `ε`. Its kinds differ and
  its target is not a cutting path, so `false_of_shortPair_succ` refutes it.

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

/-- The side words of a class are admissible when the class word is. -/
theorem side_admissible (Q : OsinLemma94ClassPolygons P) {k : Fin P.count} {i s : ℕ}
    (hs : s ∈ Q.classSides k i)
    (hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i)) :
    HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (P.word k s) := by
  intro letter hletter
  refine hadm letter ?_
  rw [Q.word_eq]
  exact List.mem_flatMap.mpr ⟨s, hs, List.mem_append_left _ hletter⟩

/-- **The one-step side pair.**  A step `[x, x + 1]` inside a side of an (A1) class `i` and a step
`[y, y + 1]` inside a side of a long class `i'` of a different, non-cutting kind, with both cross
distances `d(v(y + 1), v(x))` and `d(v(y), v(x + 1))` at most `ε`, give a contradiction once
`ε ≥ 3`. -/
theorem false_of_sideSteps (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps) {k : Fin P.count}
    {i i' s t off off' x y : ℕ} (hi : i < Q.classCount k) (hi' : i' < Q.classCount k)
    (hii' : i ≠ i') (hrel : i ∈ Q.relatorClasses k) (hlong : i' ∈ Q.longClasses k)
    (hadm : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i))
    (hadm' : HullSC.RelWord.IsAdmissible (symmetricLabelAlphabet D) (Q.word k i'))
    (hcut : Q.classKind k i' ≠ .cutting) (hkind : Q.classKind k i ≠ Q.classKind k i')
    (hs : Q.SideAt k i s off) (ht : Q.SideAt k i' t off')
    (hx : off ≤ x) (hx' : x + 1 ≤ off + (P.word k s).length)
    (hy : off' ≤ y) (hy' : y + 1 ≤ off' + (P.word k t).length)
    (hstart : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k i') (Q.word k i') (y + 1))
      (OsinComponents.vertex (Q.corner k i) (Q.word k i) x) ≤ eps)
    (hend : wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k i') (Q.word k i') y)
      (OsinComponents.vertex (Q.corner k i) (Q.word k i) (x + 1)) ≤ eps) : False := by
  obtain ⟨-, j, hj⟩ : 2 ≤ Q.classCount k ∧ ∃ j, Q.classKind k i = .cell j := hrel
  have hsmem := Q.mem_of_sideAt hs
  have htmem := Q.mem_of_sideAt ht
  have hks := Q.kind_eq k i hi s hsmem
  have hkt := Q.kind_eq k i' hi' t htmem
  have hst : s ≠ t := fun h => Q.classSides_disjoint k hi hi' hii' hsmem (h ▸ htmem)
  have eA := Q.vertex_eq_of_sideAt hi hs hx (by omega)
  have eA' := Q.vertex_eq_of_sideAt hi hs (x := x + 1) (by omega) hx'
  have eB := Q.vertex_eq_of_sideAt hi' ht (x := y + 1) (by omega) hy'
  have eB' := Q.vertex_eq_of_sideAt hi' ht hy (by omega)
  rw [eB, eA, wordDist_left_invariant] at hstart
  rw [wordDist_comm (symmetricLabelAlphabet D).alphabet.symmetricGenerating, eA', eB',
    wordDist_left_invariant] at hend
  obtain ⟨cs, hcs⟩ := GroupApproximation.GGT.OsinComponents.existsGeodesicWord
    (symmetricLabelAlphabet D) (OsinComponents.vertex (P.corner k t) (P.word k t) (y + 1 - off'))
    (OsinComponents.vertex (P.corner k s) (P.word k s) (x - off))
  obtain ⟨ce, hce⟩ := GroupApproximation.GGT.OsinComponents.existsGeodesicWord
    (symmetricLabelAlphabet D) (OsinComponents.vertex (P.corner k s) (P.word k s) (x + 1 - off))
    (OsinComponents.vertex (P.corner k t) (P.word k t) (y - off'))
  refine false_of_shortPair_succ heps P k
    { source := s, target := t
      source_lt := Q.lt_sideCount_of_mem k i hi s hsmem
      target_lt := Q.lt_sideCount_of_mem k i' hi' t htmem
      source_mem := show ∃ j, P.kind k s = .cell j from ⟨j, hks.trans hj⟩
      target_mem := show P.kind k t ≠ .short by rw [hkt]; exact hlong
      distinct := hst
      source_admissible := side_admissible Q hsmem hadm
      target_admissible := side_admissible Q htmem hadm'
      a := x - off, a' := x + 1 - off, b := y + 1 - off', b' := y - off'
      a_le := by omega, a'_le := by omega, b_le := by omega, b'_le := by omega
      source_forward := by omega
      startConnector := cs, endConnector := ce
      start_geodesic := hcs, end_geodesic := hce
      start_short := by rw [hcs.2.2]; omega
      end_short := by rw [hce.2.2]; omega } ?_ ?_ ?_
  · show y - off' < y + 1 - off'
    omega
  · show P.kind k t ≠ .cutting
    rw [hkt]
    exact hcut
  · show P.kind k s ≠ P.kind k t
    rw [hks, hkt]
    exact hkind

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.side_admissible
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_sideSteps
