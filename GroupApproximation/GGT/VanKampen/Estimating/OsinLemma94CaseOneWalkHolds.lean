import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalk
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseOneWalkLists
import GroupApproximation.GGT.OsinTheorem54SepSplit
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 1 of Osin's Lemma 9.4: the face walk holds

`osinLemma94CaseOneWalk` proves `OsinLemma94CaseOneWalkStatement`.

* The walk of polygon `k`, rotated to its base, is the concatenation of its sides.
* The source segment `[a, a']` and the target segment `[b', b]` are windows of that
  concatenation, at the positions where their sides start.
* Rotating the walk to the end `a'` of the source segment reads `X ++ T ++ Y ++ P`.  `Y` passes
  the base when the source side comes first, and `X` passes it when the target side comes first.
* A corner of the polygon is the value of a prefix of the concatenation, and the whole
  concatenation has value `1`, so `X` and `Y` carry the values the statement asks for.
* The windows are sub-arcs of the arcs the side kinds provide.  An arc on `∂Δ` inside one section
  ends by the end of the boundary word, so its sub-arc starts where the arc says.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open GroupApproximation.GGT.OsinComponents

namespace CaseOneWalk

section Diagram

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {Delta : DiscDiagram.{u, w, v} W}

/-- A reversed arc has as many darts as the arc. -/
theorem cyclicArc_length_reverseDarts {cycle : List Delta.toCombMap.Dart}
    (arc : CyclicArc cycle) : arc.reverseDarts.length = arc.length := by
  simp only [CyclicArc.reverseDarts, List.length_map, List.length_reverse,
    CyclicArc.darts_length]

/-- A window of a reversed arc is a reversed sub-arc. -/
theorem cyclicArc_exists_sub_reverse {cycle : List Delta.toCombMap.Dart}
    (arc : CyclicArc cycle) (t m : ℕ) (h : t + m ≤ arc.length) :
    ∃ arc' : CyclicArc cycle, arc'.length = m ∧
      arc'.reverseDarts = (arc.reverseDarts.drop t).take m := by
  obtain ⟨arc', hlen, hdarts, -⟩ := cyclicArc_exists_sub arc (arc.length - t - m) m (by omega)
  refine ⟨arc', hlen, ?_⟩
  have hD : arc.darts.length = arc.length := arc.darts_length
  simp only [CyclicArc.reverseDarts]
  rw [hdarts, ← List.map_drop, ← List.map_take, reverse_window_eq arc.darts (by omega), hD]

/-- The word of a concatenation of dart lists. -/
theorem dartWord_flatMap_eq {β : Type*} (l : List β) (f : β → List Delta.toCombMap.Dart) :
    dartWord Delta (l.flatMap f) = l.flatMap fun x => dartWord Delta (f x) := by
  simp only [dartWord, List.map_flatMap]

/-- The value of a joined dart list is the product of the values. -/
theorem walkValue_append (x y : List Delta.toCombMap.Dart) :
    RelLetter.listVal (dartWord Delta (x ++ y)) =
      RelLetter.listVal (dartWord Delta x) * RelLetter.listVal (dartWord Delta y) := by
  simp only [dartWord, List.map_append, OsinComponents.listVal_append]

/-- A prefix times the window after it is the longer prefix. -/
theorem walkValue_take_window (l : List Delta.toCombMap.Dart) {p q : ℕ} (h : p ≤ q) :
    RelLetter.listVal (dartWord Delta (l.take p)) *
        RelLetter.listVal (dartWord Delta ((l.drop p).take (q - p))) =
      RelLetter.listVal (dartWord Delta (l.take q)) := by
  rw [← walkValue_append, ← take_eq_take_append_window l h]

/-- On a walk of value `1`, a prefix times the stretch from its end round to the end of another
prefix is that other prefix. -/
theorem walkValue_take_wrap (l : List Delta.toCombMap.Dart)
    (hl : RelLetter.listVal (dartWord Delta l) = 1) (p q : ℕ) :
    RelLetter.listVal (dartWord Delta (l.take p)) *
        RelLetter.listVal (dartWord Delta (l.drop p ++ l.take q)) =
      RelLetter.listVal (dartWord Delta (l.take q)) := by
  rw [walkValue_append, ← mul_assoc, ← walkValue_append, List.take_append_drop, hl, one_mul]

/-- Two windows `[pa, pa']` and `[pb', pb]` on a rotated walk of value `1`, in either cyclic
order: some rotation reads `X`, the second window, `Y`, the first window, and `X`, `Y` join the
prefixes at the window ends. -/
theorem walk_four_windows (B F : List Delta.toCombMap.Dart) (base : ℕ)
    (hwalk : B.rotate base = F) (hl : RelLetter.listVal (dartWord Delta F) = 1)
    {pa pa' pb' pb : ℕ} (haa : pa ≤ pa') (hbb : pb' ≤ pb)
    (horder : (pa' ≤ pb' ∧ pb ≤ F.length) ∨ (pb ≤ pa ∧ pa' ≤ F.length)) :
    ∃ (X Y : List Delta.toCombMap.Dart) (r : ℕ),
      B.rotate r = X ++ (F.drop pb').take (pb - pb') ++ Y ++ (F.drop pa).take (pa' - pa) ∧
        RelLetter.listVal (dartWord Delta (F.take pa')) *
            RelLetter.listVal (dartWord Delta X) =
          RelLetter.listVal (dartWord Delta (F.take pb')) ∧
        RelLetter.listVal (dartWord Delta (F.take pb)) *
            RelLetter.listVal (dartWord Delta Y) =
          RelLetter.listVal (dartWord Delta (F.take pa)) := by
  rcases horder with ⟨h2, h4⟩ | ⟨h2, h4⟩
  · refine ⟨(F.drop pa').take (pb' - pa'), F.drop pb ++ F.take pa, base + pa', ?_,
      walkValue_take_window F h2, walkValue_take_wrap F hl pb pa⟩
    rw [← List.rotate_rotate, hwalk, rotate_four_inside F haa h2 hbb h4]
  · refine ⟨F.drop pa' ++ F.take pb', (F.drop pb).take (pa - pb), base + pa', ?_,
      walkValue_take_wrap F hl pa' pb', walkValue_take_window F h2⟩
    rw [← List.rotate_rotate, hwalk, rotate_four_wrap F hbb h2 haa h4]

end Diagram

section Polygons

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}

/-- A side word has one letter per dart. -/
theorem polygon_length_word (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) (i : ℕ) :
    (P.word k i).length = (P.sideDarts k i).length := by
  simp only [OsinLemma94RealizedPolygons.word, dartWord, List.length_map]

/-- The concatenated sides of a polygon have value `1`. -/
theorem polygon_walk_value (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) :
    RelLetter.listVal (dartWord S.diagram
      ((List.range (P.sideCount k)).flatMap (P.sideDarts k))) = 1 := by
  rw [dartWord_flatMap_eq]
  exact P.closed k

/-- The vertex `t` letters into side `i` is the value of the prefix of the concatenated sides
that ends there. -/
theorem polygon_vertex_eq (P : OsinLemma94RealizedPolygons S) (k : Fin P.count) {i t : ℕ}
    (hi : i < P.sideCount k) (ht : t ≤ (P.sideDarts k i).length) :
    vertex (P.corner k i) (P.word k i) t =
      RelLetter.listVal (dartWord S.diagram
        (((List.range (P.sideCount k)).flatMap (P.sideDarts k)).take
          (((List.range i).flatMap (P.sideDarts k)).length + t))) := by
  obtain ⟨rest, hrest⟩ := rangeFlatMap_split (P.sideDarts k) hi
  have h1 : ((List.range i).flatMap (P.sideDarts k)).length ≤
      ((List.range i).flatMap (P.sideDarts k)).length + t := Nat.le_add_right _ _
  have hc : P.corner k i =
      RelLetter.listVal ((List.range i).flatMap fun x => dartWord S.diagram (P.sideDarts k x)) :=
    rfl
  have hw : (P.word k i).take t = dartWord S.diagram ((P.sideDarts k i).take t) := by
    simp only [OsinLemma94RealizedPolygons.word, dartWord, List.map_take]
  rw [OsinComponents.vertex_eq_mul_listVal_take, hrest, List.take_append,
    List.take_of_length_le h1, Nat.add_sub_cancel_left, List.take_append_of_le_length ht,
    walkValue_append, dartWord_flatMap_eq, hc, hw]

/-- The two segments of a connector pair on the walk of polygon `k`, before the arcs of the side
kinds replace them. -/
theorem polygon_four_windows (P : OsinLemma94RealizedPolygons S) (k : Fin P.count)
    {s t a a' b b' : ℕ} (hs : s < P.sideCount k) (ht : t < P.sideCount k) (hst : s ≠ t)
    (haa : a ≤ a') (ha' : a' ≤ (P.sideDarts k s).length)
    (hbb : b' ≤ b) (hb : b ≤ (P.sideDarts k t).length) :
    ∃ (X Y : List S.diagram.toCombMap.Dart) (r : ℕ),
      (S.diagram.faceBoundary (P.face k)).darts.rotate r =
          X ++ ((P.sideDarts k t).drop b').take (b - b') ++ Y ++
            ((P.sideDarts k s).drop a).take (a' - a) ∧
        vertex (P.corner k s) (P.word k s) a' * RelLetter.listVal (dartWord S.diagram X) =
          vertex (P.corner k t) (P.word k t) b' ∧
        vertex (P.corner k t) (P.word k t) b * RelLetter.listVal (dartWord S.diagram Y) =
          vertex (P.corner k s) (P.word k s) a := by
  have hls := rangeFlatMap_length_le (P.sideDarts k) hs
  have hlt := rangeFlatMap_length_le (P.sideDarts k) ht
  have horder : (((List.range s).flatMap (P.sideDarts k)).length + a' ≤
          ((List.range t).flatMap (P.sideDarts k)).length + b' ∧
        ((List.range t).flatMap (P.sideDarts k)).length + b ≤
          ((List.range (P.sideCount k)).flatMap (P.sideDarts k)).length) ∨
      (((List.range t).flatMap (P.sideDarts k)).length + b ≤
          ((List.range s).flatMap (P.sideDarts k)).length + a ∧
        ((List.range s).flatMap (P.sideDarts k)).length + a' ≤
          ((List.range (P.sideCount k)).flatMap (P.sideDarts k)).length) := by
    rcases Nat.lt_or_gt_of_ne hst with h | h
    · have := rangeFlatMap_length_le (P.sideDarts k) h
      exact Or.inl ⟨by omega, by omega⟩
    · have := rangeFlatMap_length_le (P.sideDarts k) h
      exact Or.inr ⟨by omega, by omega⟩
  obtain ⟨X, Y, r, hrot, hX, hY⟩ := walk_four_windows _ _ (P.base k) (P.walk k)
    (polygon_walk_value P k) (Nat.add_le_add_left haa _) (Nat.add_le_add_left hbb _) horder
  refine ⟨X, Y, r, ?_, ?_, ?_⟩
  · have e1 : ((List.range t).flatMap (P.sideDarts k)).length + b -
        (((List.range t).flatMap (P.sideDarts k)).length + b') = b - b' := by omega
    have e2 : ((List.range s).flatMap (P.sideDarts k)).length + a' -
        (((List.range s).flatMap (P.sideDarts k)).length + a) = a' - a := by omega
    rw [hrot, e1, e2, rangeFlatMap_drop_take (P.sideDarts k) ht (by omega),
      rangeFlatMap_drop_take (P.sideDarts k) hs (by omega)]
  · rw [polygon_vertex_eq P k hs ha', polygon_vertex_eq P k ht (by omega)]
    exact hX
  · rw [polygon_vertex_eq P k ht hb, polygon_vertex_eq P k hs (by omega)]
    exact hY

end Polygons

end CaseOneWalk

open CaseOneWalk

/-- **The Case 1 face walk.**  `OsinLemma94CaseOneWalkStatement` holds: for a backwards
connector pair of a polygon whose target side is not a cutting path, some rotation of the face
walk reads `X ++ T ++ Y ++ P` with the arcs, sections and corner values the statement records. -/
theorem osinLemma94CaseOneWalk : OsinLemma94CaseOneWalkStatement.{u, w, v} := by
  intro G _ Lambda W D E lambda c eps Delta cuts S P k C hbb hcut
  obtain ⟨j, hj⟩ : ∃ j, P.kind k C.source = .cell j := C.source_mem
  have htgt : P.kind k C.target ≠ .short := C.target_mem
  have hs := C.source_lt
  have ht := C.target_lt
  have hfwd := C.source_forward
  have ha' : C.a' ≤ (P.sideDarts k C.source).length :=
    C.a'_le.trans_eq (polygon_length_word P k _)
  have hb : C.b ≤ (P.sideDarts k C.target).length :=
    C.b_le.trans_eq (polygon_length_word P k _)
  obtain ⟨X, Y, r, hrot, hX, hY⟩ :=
    polygon_four_windows P k hs ht C.distinct (le_of_lt hfwd) ha' (le_of_lt hbb) hb
  obtain ⟨sarc, hsarc⟩ := P.cell_arc k C.source j hs hj
  have hsl : (P.sideDarts k C.source).length = sarc.length := by
    rw [hsarc, cyclicArc_length_reverseDarts]
  obtain ⟨sarc', hslen, hsdarts⟩ :=
    cyclicArc_exists_sub_reverse sarc C.a (C.a' - C.a) (by omega)
  rw [hsarc, ← hsdarts] at hrot
  have hs0 : 0 < sarc'.length := by
    rw [hslen]
    omega
  cases hkt : P.kind k C.target with
  | cutting => exact absurd hkt hcut
  | short => exact absurd hkt htgt
  | cell j' =>
    obtain ⟨tarc, htarc⟩ := P.cell_arc k C.target j' ht hkt
    have htl : (P.sideDarts k C.target).length = tarc.length := by
      rw [htarc, cyclicArc_length_reverseDarts]
    obtain ⟨tarc', htlen, htdarts⟩ :=
      cyclicArc_exists_sub_reverse tarc C.b' (C.b - C.b') (by omega)
    rw [htarc, ← htdarts] at hrot
    have h0 : 0 < tarc'.length := by
      rw [htlen]
      omega
    refine ⟨j, some j', sarc', tarc', X, Y, r, hrot, hs0, h0, hj, ?_, ?_, hX, hY⟩
    · intro j0 h
      cases h
      first | rfl | exact hkt
    · intro h
      cases h
  | boundary j' =>
    obtain ⟨hj', barc, hbsd, hlo, hhi⟩ := P.boundary_arc k C.target j' ht hkt
    have hbl : (P.sideDarts k C.target).length = barc.length := by
      rw [hbsd, CyclicArc.darts_length]
    obtain ⟨tarc', htlen, htdarts, htstart⟩ :=
      cyclicArc_exists_sub barc C.b' (C.b - C.b') (by omega)
    rw [hbsd, ← htdarts] at hrot
    have hcyc : (targetDarts S.diagram none).length = Delta.boundaryWord.length := by
      have e := congrArg List.length (dartWord_outerDarts S.diagram)
      rw [S.equiv.boundaryWord_eq, dartWord, List.length_map] at e
      exact e
    have hlast := cuts.cut_mono (Fin.le_last (⟨j' + 1, by omega⟩ : Fin (cuts.count + 1)))
    rw [cuts.cut_last] at hlast
    have hst' := htstart (by omega)
    have h0 : 0 < tarc'.length := by
      rw [htlen]
      omega
    refine ⟨j, none, sarc', tarc', X, Y, r, hrot, hs0, h0, hj, ?_, ?_, hX, hY⟩
    · intro j0 h
      cases h
    · intro _
      refine ⟨⟨j', hj'⟩, ?_, ?_⟩
      · have hlo' : cuts.cut (Fin.castSucc ⟨j', hj'⟩) ≤ barc.start.1 := hlo
        rw [hst']
        omega
      · have hhi' : barc.start.1 + barc.length ≤ cuts.cut (Fin.succ ⟨j', hj'⟩) := hhi
        rw [hst', htlen]
        omega

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94CaseOneWalk

end GroupApproximation.GGT.VanKampen
