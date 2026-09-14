import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassGapHairModel
import GroupApproximation.GGT.DGOPolygonGeodesicChain
import GroupApproximation.Meta.AxiomGuard

/-!
# Moving the endpoints of a class-word connector pair out of the gaps

Osin (math/0411039v3, §9), proof of Lemma 9.4, Cases 1 and 2, on class words.  A connector pair can
have an endpoint strictly inside a gap (`OsinLemma94ClassPolygons.GapEndpoint`).  At a hair tip no
region surgery reaches that vertex (`OsinLemma94ClassGapHairModel`).  The two-threshold spelling of the
class cases (lane ct-bilateral-cell, `OsinLemma94ClassCasesTwoThresholdInput`) avoids the shape: its
pairs have connectors shorter than `ε − B` and segments longer than `ε + B`, with
`B = ⌈(c + 2) / λ⌉₊`, and every endpoint inside a gap moves to a gap corner.

* `SideAt.eq_or_block_le`: two sides of one class are the same side at the same offset, or the block of
  one (its side word and its gap) ends before the other starts.
* `not_inGap_corner`: a gap corner lies strictly inside no gap.
* `wordDist_vertex_le_of_near`: positions at most `d` apart give vertices at most `d` apart.
* `exists_cornerMove`: a position of a class word in `N1 ∪ N2` moves to a position inside no gap, by at
  most `⌊B / 2⌋` letters (the nearer corner of its gap, of length at most `B` by `gap_length_le`).
* `exists_cornerPair_of_twoThreshold`: a backwards pair at threshold `ε − B` whose segments are longer
  than `ε + B` gives a backwards pair at threshold `ε` with no endpoint inside a gap, on the same two
  classes.  Each endpoint moves by at most `⌊B / 2⌋`, so the rebuilt geodesic connectors grow by at most
  `B` and the segments shrink by at most `B`; the orientations survive because a segment of length
  above `ε > B` cannot fold back within `B` letters.

The threshold gate of the two-threshold producer: the metric half bounds cross distances by the
closeness constant `12 ((δ + 6) + 1) + 2 κ` (`OsinUnboundScale.epsilon_large`), with the Morse radius `κ`
depending on `δ, λ, c` only, and the segments below by `β − 2 κ` with `β = (λ √ρ / 240 − c) / 1000`
(`OsinUnboundScale.shortcut_shortens`), with `ρ` chosen after `ε`.  So `ε₀ > 12 ((δ + 6) + 1) + 2 κ + B`
and a scale at `ε + B` give both thresholds, in the order of Osin's (36).

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's Lemma 9.4
inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.WordMetric

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **Two sides of one class, by offset.**  Either they are the same side at the same offset, or the
block of one side, its word and its gap, ends before the other side starts. -/
theorem SideAt.eq_or_block_le {Q : OsinLemma94ClassPolygons P} {k : Fin P.count}
    {i s t off off' : ℕ} (hs : Q.SideAt k i s off) (ht : Q.SideAt k i t off') :
    (s = t ∧ off = off') ∨
      off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length ≤ off' ∨
      off' + (P.word k t).length + (Embedded.dartWord S.diagram (Q.gap k t)).length ≤ off := by
  obtain ⟨L1, L2, hL, hoff⟩ := hs
  obtain ⟨L1', L2', hL', hoff'⟩ := ht
  rw [hL] at hL'
  subst hoff hoff'
  rcases List.append_eq_append_iff.1 hL' with ⟨M0, h1, h2⟩ | ⟨N0, h1, h2⟩
  · cases M0 with
    | nil =>
      simp only [List.append_nil] at h1
      simp only [List.nil_append, List.cons.injEq] at h2
      exact Or.inl ⟨h2.1, by rw [h1]⟩
    | cons x M =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      refine Or.inr (Or.inl ?_)
      rw [h1]
      simp only [List.flatMap_append, List.flatMap_cons, List.length_append]
      omega
  · cases N0 with
    | nil =>
      simp only [List.append_nil] at h1
      simp only [List.nil_append, List.cons.injEq] at h2
      exact Or.inl ⟨h2.1.symm, by rw [h1]⟩
    | cons x M =>
      simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, -⟩ := h2
      refine Or.inr (Or.inr ?_)
      rw [h1]
      simp only [List.flatMap_append, List.flatMap_cons, List.length_append]
      omega

/-- **A gap corner lies strictly inside no gap.** -/
theorem not_inGap_corner {Q : OsinLemma94ClassPolygons P} {k : Fin P.count} {i s off y : ℕ}
    (hs : Q.SideAt k i s off)
    (hy : y = off + (P.word k s).length ∨
      y = off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length) :
    ¬ Q.InGap k i y := by
  rintro ⟨t, off', ht, h1, h2⟩
  rcases hy with rfl | rfl <;>
    rcases hs.eq_or_block_le ht with ⟨rfl, rfl⟩ | hle | hle <;> omega

/-- **Nearby positions, nearby vertices.**  Positions of an admissible word at most `d` apart give
vertices at most `d` apart. -/
theorem wordDist_vertex_le_of_near {D' : RelGenSet G Lambda} {w : List (RelLetter G Lambda)}
    (hlet : HullSC.RelWord.IsAdmissible D' w) (g : G) {x y d : ℕ} (hx : x ≤ w.length)
    (hy : y ≤ w.length) (hxy : x ≤ y + d) (hyx : y ≤ x + d) :
    wordDist D'.alphabet.carrier (OsinComponents.vertex g w x) (OsinComponents.vertex g w y) ≤
      d := by
  rcases le_total x y with h | h
  · have hd := OsinComponents.wordDist_vertex_le' D' hlet g h hy
    omega
  · rw [wordDist_comm D'.alphabet.symmetricGenerating]
    have hd := OsinComponents.wordDist_vertex_le' D' hlet g h hx
    omega

/-- **The corner move of one endpoint.**  A position of a class word in `N1 ∪ N2` moves to a position
inside no gap, by at most `⌊⌈(c + 2) / λ⌉₊ / 2⌋` letters: a gap-interior position to the nearer corner
of its gap, any other position nowhere. -/
theorem exists_cornerMove (Q : OsinLemma94ClassPolygons P) (hlambda : 0 < lambda)
    {k : Fin P.count} {i x : ℕ} (hi : i < Q.classCount k)
    (hmem : i ∈ Q.relatorClasses k ∨ i ∈ Q.longClasses k) (hx : x ≤ (Q.word k i).length) :
    ∃ y, y ≤ (Q.word k i).length ∧ ¬ Q.InGap k i y ∧
      y ≤ x + ⌈(c + 2) / lambda⌉₊ / 2 ∧ x ≤ y + ⌈(c + 2) / lambda⌉₊ / 2 := by
  by_cases hin : Q.InGap k i x
  · obtain ⟨s, off, hs, h1, h2⟩ := hin
    have hgap := Q.gap_length_le hlambda hi hmem hs
    obtain ⟨A, R, hw, hA⟩ := hs.word_split
    have hlen : off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length ≤
        (Q.word k i).length := by
      rw [hw]
      simp only [List.length_append]
      omega
    by_cases hnear : x - (off + (P.word k s).length) ≤
        off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length - x
    · exact ⟨off + (P.word k s).length, by omega, not_inGap_corner hs (Or.inl rfl), by omega,
        by omega⟩
    · exact ⟨off + (P.word k s).length + (Embedded.dartWord S.diagram (Q.gap k s)).length, hlen,
        not_inGap_corner hs (Or.inr rfl), by omega, by omega⟩
  · exact ⟨x, hx, hin, by omega, by omega⟩

/-- **The corner pair of a two-threshold pair.**  A backwards class-word connector pair at threshold
`ε − B`, `B = ⌈(c + 2) / λ⌉₊`, whose two segments are longer than `ε + B`, gives a backwards pair at
threshold `ε` on the same two classes with no endpoint strictly inside a gap. -/
theorem exists_cornerPair_of_twoThreshold (Q : OsinLemma94ClassPolygons P) (hlambda : 0 < lambda)
    (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) (eps - ⌈(c + 2) / lambda⌉₊))
    (hlongS : eps + ⌈(c + 2) / lambda⌉₊ < wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a'))
    (hlongT : eps + ⌈(c + 2) / lambda⌉₊ < wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b'))
    (hback : C.b' < C.b) :
    ∃ C' : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
        (Q.relatorClasses k) (Q.longClasses k) eps,
      C'.b' < C'.b ∧ ¬ Q.GapEndpoint k C' ∧ C'.source = C.source ∧ C'.target = C.target := by
  have hS := (symmetricLabelAlphabet D).alphabet.symmetricGenerating
  have hBeps : ⌈(c + 2) / lambda⌉₊ < eps := by
    have h := C.start_short
    omega
  obtain ⟨a1, ha1, hga1, ha1u, ha1d⟩ :=
    Q.exists_cornerMove hlambda C.source_lt (Or.inl C.source_mem) C.a_le
  obtain ⟨a1', ha1', hga1', ha1'u, ha1'd⟩ :=
    Q.exists_cornerMove hlambda C.source_lt (Or.inl C.source_mem) C.a'_le
  obtain ⟨b1, hb1, hgb1, hb1u, hb1d⟩ :=
    Q.exists_cornerMove hlambda C.target_lt (Or.inr C.target_mem) C.b_le
  obtain ⟨b1', hb1', hgb1', hb1'u, hb1'd⟩ :=
    Q.exists_cornerMove hlambda C.target_lt (Or.inr C.target_mem) C.b'_le
  have hdA := wordDist_vertex_le_of_near C.source_admissible (Q.corner k C.source) C.a_le ha1
    ha1d ha1u
  have hdA' := wordDist_vertex_le_of_near C.source_admissible (Q.corner k C.source) C.a'_le ha1'
    ha1'd ha1'u
  have hdB := wordDist_vertex_le_of_near C.target_admissible (Q.corner k C.target) C.b_le hb1
    hb1d hb1u
  have hdB' := wordDist_vertex_le_of_near C.target_admissible (Q.corner k C.target) C.b'_le hb1'
    hb1'd hb1'u
  have hsegS : eps < wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1') := by
    have t1 := wordDist_triangle hS
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a')
    have t2 := wordDist_triangle hS
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1')
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a')
    have c1 := wordDist_comm hS
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1')
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a')
    omega
  have hsegT : eps < wordDist (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1)
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1') := by
    have t1 := wordDist_triangle hS
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1)
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b')
    have t2 := wordDist_triangle hS
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1)
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1')
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b')
    have c1 := wordDist_comm hS
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1')
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b')
    omega
  have hforward : a1 < a1' := by
    by_contra hge
    push Not at hge
    have hd := OsinComponents.wordDist_vertex_le' (symmetricLabelAlphabet D) C.source_admissible
      (Q.corner k C.source) hge ha1
    rw [wordDist_comm hS] at hd
    have hsf := C.source_forward
    omega
  have hbackward : b1' < b1 := by
    by_contra hge
    push Not at hge
    have hd := OsinComponents.wordDist_vertex_le' (symmetricLabelAlphabet D) C.target_admissible
      (Q.corner k C.target) hge hb1'
    omega
  obtain ⟨s', hs'⟩ := OsinComponents.existsGeodesicWord (symmetricLabelAlphabet D)
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1)
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1)
  obtain ⟨t', ht'⟩ := OsinComponents.existsGeodesicWord (symmetricLabelAlphabet D)
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1')
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1')
  have hshort1 : s'.length < eps := by
    have t1 := wordDist_triangle hS
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1)
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1)
    have t2 := wordDist_triangle hS
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a)
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1)
    have c1 := wordDist_comm hS
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1)
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b)
    have hlen := hs'.2.2
    have hold := C.start_geodesic.2.2
    have hshort := C.start_short
    omega
  have hshort2 : t'.length < eps := by
    have t1 := wordDist_triangle hS
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1')
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a')
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1')
    have t2 := wordDist_triangle hS
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a')
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b')
      (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) b1')
    have c1 := wordDist_comm hS
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) a1')
      (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a')
    have hlen := ht'.2.2
    have hold := C.end_geodesic.2.2
    have hshort := C.end_short
    omega
  refine ⟨{
    source := C.source, target := C.target, source_lt := C.source_lt, target_lt := C.target_lt
    source_mem := C.source_mem, target_mem := C.target_mem, distinct := C.distinct
    source_admissible := C.source_admissible, target_admissible := C.target_admissible
    a := a1, a' := a1', b := b1, b' := b1'
    a_le := ha1, a'_le := ha1', b_le := hb1, b'_le := hb1', source_forward := hforward
    source_long := hsegS, target_long := hsegT
    startConnector := s', endConnector := t', start_geodesic := hs', end_geodesic := ht'
    start_short := hshort1, end_short := hshort2 }, hbackward, ?_, rfl, rfl⟩
  rintro (h | h | h | h)
  · exact hga1 h
  · exact hga1' h
  · exact hgb1 h
  · exact hgb1' h

end OsinLemma94ClassPolygons

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms OsinLemma94ClassPolygons.SideAt.eq_or_block_le
#audit_axioms OsinLemma94ClassPolygons.not_inGap_corner
#audit_axioms OsinLemma94ClassPolygons.exists_cornerMove
#audit_axioms OsinLemma94ClassPolygons.exists_cornerPair_of_twoThreshold
