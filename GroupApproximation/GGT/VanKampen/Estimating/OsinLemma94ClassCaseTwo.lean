import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassRunPositions
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94CaseTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# Case 2 of Osin's Lemma 9.4 on class words

Osin (math/0411039v3, §9), Lemma 9.4, Case 2: "This contradicts our assumption that `∑ l(t_i)` is
minimal."  A backwards class-word pair whose target class is a cutting path.  A cutting class is one
side (`OsinLemma94ClassPolygons.single`), so only the source runs across gaps.  The face walk reads the
side run of the source class, not its gaps (`OsinLemma94ClassPolygons.class_four_windows`), and the
reverse darts of that run lie on relator cells, side by side.  So the argument of
`osinLemma94CaseTwo_false` goes through unsplit: the connector with the value of the stretch across the
target is inserted across the face, the cutting path is removed, and `DartMinimal` fails.

* `osinLemma94ClassCaseTwo_false`: a backwards class-word pair with no endpoint strictly inside a gap and
  a cutting target class gives a contradiction, once `ε ≥ 3`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate
open CaseTwoWalk

/-- **Case 2 on class words.**  Once `ε ≥ 3`, a dart-minimal family has no backwards class-word pair
of polygon `k`, with no endpoint strictly inside a gap, whose target class is a cutting path. -/
theorem osinLemma94ClassCaseTwo_false
    (hinsert : GloballyDistinguishedSectionFamily.SeparatedCornerInsertionInput.{u, w, v})
    {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (RelLetter G Lambda))}
    {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ} (heps : 3 ≤ eps)
    {Delta : DiscDiagram.{u, w, v} W} {cuts : SectionCuts D lambda c Delta.boundaryWord}
    {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts} (hS : S.DartMinimal)
    (P : OsinLemma94RealizedPolygons S) (Q : OsinLemma94ClassPolygons P) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hback : C.b' < C.b) (hcut : Q.classKind k C.target = .cutting)
    (hnogap : ¬ Q.GapEndpoint k C) : False := by
  obtain ⟨N⟩ := C.exists_nonempty_connectors (symmetricLabelAlphabet.symmetric D) (by omega)
  have hcells : ∀ cell ∈ S.diagram.relatorCells, cell.face ≠ P.face k := by
    intro cell hcell
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hcell
    exact P.face_not_cell k j
  have hf : S.UnselectedGFace (P.face k) := ⟨P.face_ne_outer k, hcells, P.face_unselected k⟩
  obtain ⟨-, jcell, hjcell⟩ : 2 ≤ Q.classCount k ∧ ∃ j, Q.classKind k C.source = .cell j :=
    C.source_mem
  have hi := C.source_lt
  have hi' := C.target_lt
  -- The cutting class is one side `t`.
  obtain ⟨t, htside⟩ := List.length_eq_one_iff.mp (Q.single k C.target hi' (Or.inl hcut))
  have htmem : t ∈ Q.classSides k C.target := by
    rw [htside]
    exact List.mem_singleton_self t
  have ht : t < P.sideCount k := Q.lt_sideCount_of_mem k C.target hi' t htmem
  have hkt : P.kind k t = .cutting := (Q.kind_eq k C.target hi' t htmem).trans hcut
  have hwordT : Q.word k C.target = P.word k t := Q.word_eq_of_eq_singleton k C.target hi' htside
  have hrunT : Q.sideRun k C.target = P.sideDarts k t := by
    show (Q.classSides k C.target).flatMap (P.sideDarts k) = P.sideDarts k t
    rw [htside, List.flatMap_singleton]
  -- The endpoints lie off the gaps.
  have hngA : ¬ Q.InGap k C.source C.a := fun h => hnogap (Or.inl h)
  have hngA' : ¬ Q.InGap k C.source C.a' := fun h => hnogap (Or.inr (Or.inl h))
  have hngB : ¬ Q.InGap k C.target C.b := fun h => hnogap (Or.inr (Or.inr (Or.inl h)))
  have hngB' : ¬ Q.InGap k C.target C.b' := fun h => hnogap (Or.inr (Or.inr (Or.inr h)))
  have hbT : C.b ≤ (P.word k t).length := by
    rw [← hwordT]
    exact C.b_le
  have hrunB : Q.runPos k (Q.classSides k C.target) C.b = C.b := by
    rw [htside]
    exact Q.runPos_singleton k hbT
  have hrunB' : Q.runPos k (Q.classSides k C.target) C.b' = C.b' := by
    rw [htside]
    exact Q.runPos_singleton k (by omega)
  -- Vertices and positions on the side runs.
  have hvA := Q.vertex_eq_classWalk_take k hi hngA
  have hvA' := Q.vertex_eq_classWalk_take k hi hngA'
  have hvB := Q.vertex_eq_classWalk_take k hi' hngB
  have hvB' := Q.vertex_eq_classWalk_take k hi' hngB'
  rw [hrunB] at hvB
  rw [hrunB'] at hvB'
  have hpaa : Q.runPos k (Q.classSides k C.source) C.a ≤
      Q.runPos k (Q.classSides k C.source) C.a' :=
    Q.runPos_mono k (Q.classSides k C.source) C.source_forward.le
  have hpa' := Q.runPos_le_sideRun k C.source C.a'
  have hpstrict : Q.runPos k (Q.classSides k C.source) C.a <
      Q.runPos k (Q.classSides k C.source) C.a' := by
    by_contra hge
    have heq : Q.runPos k (Q.classSides k C.source) C.a =
        Q.runPos k (Q.classSides k C.source) C.a' := by
      omega
    have hl := C.source_long
    rw [hvA, hvA', heq, WordMetric.wordDist_self] at hl
    omega
  have hbrun : C.b ≤ (Q.sideRun k C.target).length := by
    rw [hrunT, ← CaseOneWalk.polygon_length_word P k t]
    exact hbT
  obtain ⟨X, Y, r, hwalk, hX, hY⟩ :=
    Q.class_four_windows k hi hi' C.distinct hpaa hpa' hback.le hbrun
  have hX' : OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a' *
      RelLetter.listVal (dartWord S.diagram X) =
        OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b' := by
    rw [hvA', hvB']
    exact hX
  have hY' : OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) C.b *
      RelLetter.listVal (dartWord S.diagram Y) =
        OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) C.a := by
    rw [hvB, hvA]
    exact hY
  -- The target segment is longer than `ε`.
  have hlong : eps < C.b - C.b' := by
    have h1 := C.target_long
    rw [WordMetric.wordDist_comm (symmetricLabelAlphabet D).alphabet.symmetricGenerating] at h1
    exact lt_of_lt_of_le h1 (OsinComponents.wordDist_vertex_le' (symmetricLabelAlphabet D)
      (w := Q.word k C.target) C.target_admissible (Q.corner k C.target) hback.le C.b_le)
  obtain ⟨Tw, hTw⟩ : ∃ Tw, Tw = ((P.sideDarts k t).drop C.b').take (C.b - C.b') := ⟨_, rfl⟩
  obtain ⟨Sw, hSw⟩ : ∃ Sw, Sw = ((Q.sideRun k C.source).drop
      (Q.runPos k (Q.classSides k C.source) C.a)).take
        (Q.runPos k (Q.classSides k C.source) C.a' - Q.runPos k (Q.classSides k C.source) C.a) :=
    ⟨_, rfl⟩
  rw [hrunT, ← hTw, ← hSw] at hwalk
  have hTwlen : Tw.length = C.b - C.b' := by
    have hb : C.b ≤ (P.sideDarts k t).length := by
      rw [← CaseOneWalk.polygon_length_word P k t]
      exact hbT
    rw [hTw, List.length_take, List.length_drop]
    omega
  have hTwne : Tw ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hSwne : Sw ≠ [] := by
    refine List.ne_nil_of_length_pos ?_
    rw [hSw, List.length_take, List.length_drop]
    omega
  have hTwt : ∀ d ∈ Tw, d ∈ P.sideDarts k t := by
    intro d hd
    rw [hTw] at hd
    exact List.mem_of_mem_drop (List.mem_of_mem_take hd)
  have hSws : ∀ d ∈ Sw, ∃ s ∈ Q.classSides k C.source, d ∈ P.sideDarts k s := by
    intro d hd
    rw [hSw] at hd
    have hmem : d ∈ (Q.classSides k C.source).flatMap (P.sideDarts k) :=
      List.mem_of_mem_drop (List.mem_of_mem_take hd)
    exact List.mem_flatMap.mp hmem
  have hruns : S.RunsBackAcross Tw := by
    rw [hTw]
    exact runsBackAcross_window P k ht hkt _ _
  -- The walk from four bases.
  have hwalkXT : (S.diagram.faceBoundary (P.face k)).darts.rotate r = X ++ Tw ++ (Y ++ Sw) := by
    rw [hwalk]
    simp only [List.append_assoc]
  have hwalkX : (S.diagram.faceBoundary (P.face k)).darts.rotate r = X ++ (Tw ++ (Y ++ Sw)) := by
    rw [hwalk]
    simp only [List.append_assoc]
  have hwalkT : (S.diagram.faceBoundary (P.face k)).darts.rotate (r + X.length) =
      Tw ++ (Y ++ (Sw ++ X)) := by
    rw [rotate_add_length_of_eq hwalkX]
    simp only [List.append_assoc]
  have hwalkYS : (S.diagram.faceBoundary (P.face k)).darts.rotate (r + (X ++ Tw).length) =
      Y ++ Sw ++ (X ++ Tw) := rotate_add_length_of_eq hwalkXT
  have hwalkY : (S.diagram.faceBoundary (P.face k)).darts.rotate (r + (X ++ Tw).length) =
      Y ++ (Sw ++ X ++ Tw) := by
    rw [hwalkYS]
    simp only [List.append_assoc]
  -- Where the reverse darts of the target segment lie.
  have hTwface : ∀ d ∈ Tw, S.diagram.toCombMap.faceOf d = P.face k := by
    intro d hd
    have hmem : d ∈ (S.diagram.faceBoundary (P.face k)).darts.rotate r := by
      rw [hwalk]
      simp [hd]
    exact ((S.diagram.faceBoundary (P.face k)).mem_iff _).mp (List.mem_rotate.mp hmem)
  have hnotT : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∉ Tw :=
    GloballyDistinguishedSectionFamily.alpha_not_mem_of_dartMinimal
      GloballyDistinguishedSectionFamily.pendantPathRemovalInput hS hf hwalkT hruns
  have hnotS : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∉ Sw := by
    intro d hd h
    obtain ⟨s, hs, hds⟩ := hSws _ h
    have hsl : s < P.sideCount k := Q.lt_sideCount_of_mem k C.source hi s hs
    have hks : P.kind k s = .cell jcell := (Q.kind_eq k C.source hi s hs).trans hjcell
    obtain ⟨arc, harc⟩ := P.cell_arc k s jcell hsl hks
    have hz : S.diagram.toCombMap.alpha d ∈ arc.reverseDarts := by
      rw [← harc]
      exact hds
    refine GFaceWordInsertion.faceOf_alpha_ne_of_mem_reverseDarts S.diagram hcells jcell arc hz ?_
    rw [S.diagram.toCombMap.alpha_involutive d]
    exact hTwface d hd
  have hXY : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∈ X ∨ S.diagram.toCombMap.alpha d ∈ Y := by
    intro d hd
    have hmem : S.diagram.toCombMap.alpha d ∈
        (S.diagram.faceBoundary (P.face k)).darts.rotate r :=
      List.mem_rotate.mpr (((S.diagram.faceBoundary (P.face k)).mem_iff _).mpr
        (P.cutting_internal k t ht hkt d (hTwt d hd)))
    rw [hwalk] at hmem
    simp only [List.mem_append] at hmem
    rcases hmem with ((h | h) | h) | h
    · exact Or.inl h
    · exact absurd h (hnotT d hd)
    · exact Or.inr h
    · exact absurd h (hnotS d hd)
  have hstep : ∀ (i : ℕ) (hi : i + 1 < Tw.length),
      S.diagram.toCombMap.facePerm (S.diagram.toCombMap.alpha Tw[i + 1]) =
        S.diagram.toCombMap.alpha Tw[i] := by
    intro i hi
    have hi' : i < Tw.length := by omega
    exact hruns i _ _ (List.getElem?_eq_getElem hi') (List.getElem?_eq_getElem hi)
  have hlastlt : Tw.length - 1 < Tw.length := by omega
  have hval1 : RelLetter.listVal N.endWord = RelLetter.listVal (dartWord S.diagram X) :=
    N.end_value.trans (mul_left_cancel (C.end_geodesic.2.1.trans hX'.symm))
  have hval2 : RelLetter.listVal N.startWord = RelLetter.listVal (dartWord S.diagram Y) :=
    N.start_value.trans (mul_left_cancel (C.start_geodesic.2.1.trans hY'.symm))
  rcases hXY _ (List.getElem_mem hlastlt) with hlX | hlY
  · have hallX : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∈ X := by
      have hstepX : ∀ (i : ℕ) (hi : i + 1 < Tw.length),
          S.diagram.toCombMap.alpha Tw[i + 1] ∈ X → S.diagram.toCombMap.alpha Tw[i] ∈ X := by
        intro i hi hx
        have hi' : i < Tw.length := by omega
        have h := facePerm_mem_front_of_not_mem_back hwalkXT hTwne hx
          (by rw [hstep i hi]; exact hnotT _ (List.getElem_mem hi'))
        rwa [hstep i hi] at h
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      refine getElem_of_last_of_step (Q := fun d => S.diagram.toCombMap.alpha d ∈ X) (l := Tw)
        hstepX ?_ i hi
      intro j hj hjl
      obtain rfl : j = Tw.length - 1 := by omega
      exact hlX
    obtain ⟨T, hTsum, hTcount, path', hlen', hnodup, hjoints, first, second, hfs, hfirst, hsecond,
      hsides⟩ := hinsert S (P.face k) r X (Tw ++ (Y ++ Sw)) Tw N.endWord hf hwalkX
        (by simp [hTwne]) (List.prefix_append _ _).isInfix hallX hruns N.end_nonempty
        N.end_admissible hval1
    obtain ⟨U, hUsum, hUcount⟩ :=
      GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant
        GloballyDistinguishedSectionFamily.pendantPathRemovalInput T path' first second
        (List.ne_nil_of_length_pos (by omega)) hnodup hfs hfirst hsecond hjoints hsides
    have hle := hS U (hUsum.trans hTsum)
    have hshort := N.end_short
    omega
  · have hallY : ∀ d ∈ Tw, S.diagram.toCombMap.alpha d ∈ Y := by
      have hstepY : ∀ (i : ℕ) (hi : i + 1 < Tw.length),
          S.diagram.toCombMap.alpha Tw[i + 1] ∈ Y → S.diagram.toCombMap.alpha Tw[i] ∈ Y := by
        intro i hi hy
        have hi' : i < Tw.length := by omega
        have h := facePerm_mem_front_of_not_mem_back hwalkYS hSwne hy
          (by rw [hstep i hi]; exact hnotS _ (List.getElem_mem hi'))
        rwa [hstep i hi] at h
      intro d hd
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hd
      refine getElem_of_last_of_step (Q := fun d => S.diagram.toCombMap.alpha d ∈ Y) (l := Tw)
        hstepY ?_ i hi
      intro j hj hjl
      obtain rfl : j = Tw.length - 1 := by omega
      exact hlY
    obtain ⟨T, hTsum, hTcount, path', hlen', hnodup, hjoints, first, second, hfs, hfirst, hsecond,
      hsides⟩ := hinsert S (P.face k) (r + (X ++ Tw).length) Y (Sw ++ X ++ Tw) Tw N.startWord
        hf hwalkY (by simp [hSwne]) (List.suffix_append _ _).isInfix hallY hruns
        N.start_nonempty N.start_admissible hval2
    obtain ⟨U, hUsum, hUcount⟩ :=
      GloballyDistinguishedSectionFamily.separatingPathRemovalInput_of_pendant
        GloballyDistinguishedSectionFamily.pendantPathRemovalInput T path' first second
        (List.ne_nil_of_length_pos (by omega)) hnodup hfs hfirst hsecond hjoints hsides
    have hle := hS U (hUsum.trans hTsum)
    have hshort := N.start_short
    omega

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.osinLemma94ClassCaseTwo_false
