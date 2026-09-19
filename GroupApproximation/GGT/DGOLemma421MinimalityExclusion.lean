import GroupApproximation.GGT.DGOLemma421MinimalityConnections
import GroupApproximation.GGT.DGOComponentRestriction

/-!
# Excluding the three unwanted sides of the minimality quadrilateral

A deep component internal to the source side must connect elsewhere in the
quadrilateral. Isolation in its original W-word excludes the source side
and both peripheral connectors, leaving a match on the opposite path.
-/

namespace GroupApproximation.GGT.OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- In a W3 word, maximal components of any segment remain maximal in the
whole word, including components touching the cut endpoints. -/
theorem isComp_of_segment_of_isWThree
    {D : RelGenSet G Lambda} {word : List (RelLetter G Lambda)}
    (hW3 : WWord.IsWThree D word) {start width i k : ℕ} {nu : Lambda}
    (hcomp : IsComp nu ((word.drop start).take width) i k) :
    IsComp nu word (start + i) (start + k) := by
  have hik := isComp_succ_of_isWThree (isWThree_drop_take_421 hW3 start width) hcomp
  have hi : i < ((word.drop start).take width).length := hcomp.1.trans_le hcomp.2.1
  have hiw : i < width := hi.trans_le (List.length_take_le _ _)
  have hletter := hcomp.2.2.1 i le_rfl hcomp.1 hi
  obtain ⟨x, hread⟩ : ∃ x : G,
      ((word.drop start).take width)[i]? = some (RelLetter.comp nu x) := by
    cases he : ((word.drop start).take width)[i]'hi with
    | base x => rw [he] at hletter; exact hletter.elim
    | comp label x =>
      rw [he] at hletter
      refine ⟨x, ?_⟩
      rw [List.getElem?_eq_getElem hi, he, hletter]
  have hreadWord : word[start + i]? = some (RelLetter.comp nu x) := by
    rw [← getElem?_drop_take_of_lt_421 word hiw]
    exact hread
  have hc := isComp_singleton_of_isWThree_read hW3 hreadWord
  convert hc using 1
  omega

/-- A component starting in the source segment starts a component of the
original W3 word, even if its polygon component crosses a cut endpoint. -/
theorem isCompStart_of_fourGon_source_segment
    {D : RelGenSet G Lambda} {P e f Qseg : List (RelLetter G Lambda)}
    (hW3 : WWord.IsWThree D P) {start width i : ℕ} {nu : Lambda}
    (hi : i < ((P.drop start).take width).length)
    (hstart : IsCompStart nu
      (e ++ (P.drop start).take width ++ f ++ revWord Qseg) (e.length + i)) :
    IsCompStart nu P (start + i) := by
  obtain ⟨occ, hpos, hlabel⟩ := exists_side_occurrence_of_fourGon_start_421
    (isWThree_drop_take_421 hW3 start width) hi hstart
  have hc := PeripheralOccurrence.isComp (isWThree_drop_take_421 hW3 start width) occ
  rw [hpos, hlabel] at hc
  exact ⟨start + (i + 1), isComp_of_segment_of_isWThree hW3 hc⟩


omit [Group G] in
private theorem label_eq_of_isCompOf {letter : RelLetter G Lambda} {nu lam : Lambda}
    (hnu : letter.IsCompOf nu) (hlam : letter.IsCompOf lam) : nu = lam := by
  cases letter with
  | base x => exact hnu.elim
  | comp label x => exact hnu.symm.trans hlam

/-- An isolated source component internal to the two matched source
components can only connect to the opposite path. This excludes the near
connector, the original source path, and the far connector explicitly. -/
theorem DGO421MinimalityFourGonData.exists_opposite_match
    {D : RelGenSet G Lambda} {C : ℕ}
    (hproj : ∀ (n : ℕ) (v : G) (word : List (RelLetter G Lambda)),
      IsQuasiGeodesicPolygon D 4 1 n v word →
      ∀ (nu : Lambda) (i k : ℕ), IsComp nu word i k → IsIsolated D.fam nu v word i →
        (vertex v word i)⁻¹ * vertex v word k ∈ D.relBall nu (C * n))
    {P Q : List (RelLetter G Lambda)} {vp vq : G} {lam mu nu : Lambda}
    {ip1 ip2 iq1 iq2 i : ℕ}
    (F : DGO421MinimalityFourGonData D vp vq P Q lam mu ip1 ip2 iq1 iq2)
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hW3P : WWord.IsWThree D P) (hW3Q : WWord.IsWThree D Q)
    (hnear : IsComp lam P ip1 (ip1 + 1))
    (hfar : IsComp mu P (ip2 - 1) ip2)
    (hsource : IsComp nu P i (i + 1))
    (hiso : IsIsolated D.fam nu vp P i)
    (hleft : ip1 < i) (hright : i + 1 < ip2)
    (hip2 : ip2 ≤ P.length) (hiq : iq1 ≤ iq2) (hiq2 : iq2 ≤ Q.length)
    (hdeep : (vertex vp P i)⁻¹ * vertex vp P (i + 1) ∉ D.relBall nu (C * 4)) :
    ∃ j k : ℕ, IsComp nu Q j k ∧ iq1 ≤ j ∧ k ≤ iq2 ∧
      (vertex vp P i)⁻¹ * vertex vq Q j ∈ D.fam nu := by
  let a := i - ip1
  have ha : ip1 + a = i := by dsimp [a]; omega
  have ha1 : ip1 + (a + 1) = i + 1 := by omega
  have hlenP : ((P.drop ip1).take (ip2 - ip1)).length = ip2 - ip1 :=
    length_segment P ip1 (ip2 - ip1) (by omega)
  have hlenQ : ((Q.drop iq1).take (iq2 - iq1)).length = iq2 - iq1 :=
    length_segment Q iq1 (iq2 - iq1) (by omega)
  have ha0 : 0 < a := by omega
  have haEnd : a + 1 < ((P.drop ip1).take (ip2 - ip1)).length := by omega
  have haLe : a ≤ ((P.drop ip1).take (ip2 - ip1)).length := by omega
  have ha1Le : a + 1 ≤ ((P.drop ip1).take (ip2 - ip1)).length := by omega
  have hsegment : IsComp nu ((P.drop ip1).take (ip2 - ip1)) a (a + 1) :=
    isComp_segment_of_isComp nu P (by rw [ha, ha1]; exact hsource)
      (by omega) (by omega)
  have hpolyComp : IsComp nu F.cycleWord (F.sourceIndex a) (F.sourceIndex (a + 1)) :=
    isComp_fourGon_of_isComp_side_of_interior F.near _ F.far _ nu ha0 haEnd hsegment
  have hspan : (vertex (1 : G) F.cycleWord (F.sourceIndex a))⁻¹ *
      vertex (1 : G) F.cycleWord (F.sourceIndex (a + 1)) =
        (vertex vp P i)⁻¹ * vertex vp P (i + 1) := by
    rw [F.source_vertex haLe, F.source_vertex ha1Le, ha, ha1]
    group
  have hdeepPoly : (vertex (1 : G) F.cycleWord (F.sourceIndex a))⁻¹ *
      vertex (1 : G) F.cycleWord (F.sourceIndex (a + 1)) ∉ D.relBall nu (C * 4) := by
    rw [hspan]
    exact hdeep
  obtain ⟨j, hji, hstart, hconn⟩ := exists_connected_of_deep_component hproj F.polygon
    hpolyComp hdeepPoly
  have hjlt : j < F.cycleWord.length := by
    obtain ⟨k, hk⟩ := hstart
    exact hk.1.trans_le hk.2.1
  have hletter : (F.cycleWord[j]'hjlt).IsCompOf nu := by
    obtain ⟨k, hk⟩ := hstart
    exact hk.2.2.1 j le_rfl hk.1 hjlt
  by_cases hjNear : j < F.near.length
  · have hnu : nu = lam := label_eq_of_isCompOf hletter
      (F.near_labels _ (getElem_mem_fourGon_p _ _ _ _ hjNear hjlt))
    subst nu
    have hj0 : j = 0 := by have hlen := F.near_length; omega
    subst j
    have hc := F.connected_source_of_near haLe F.near_match hconn
    rw [ha] at hc
    exact (hiso.2 ip1 (by omega) ⟨ip1 + 1, hnear⟩ (connected_symm hc)).elim
  by_cases hjSource : j < F.near.length + ((P.drop ip1).take (ip2 - ip1)).length
  · let b := j - F.near.length
    have hb : b < ((P.drop ip1).take (ip2 - ip1)).length := by dsimp [b]; omega
    have hjEq : F.sourceIndex b = j := by dsimp [sourceIndex, b]; omega
    have hs : IsCompStart nu P (ip1 + b) :=
      isCompStart_of_fourGon_source_segment hW3P hb (by rw [← hjEq] at hstart; exact hstart)
    have hc := (F.source_connection_iff haLe (le_of_lt hb)).mp
      (by rw [hjEq]; exact hconn)
    rw [ha] at hc
    have hne : ip1 + b ≠ i := by
      intro heq
      apply hji
      rw [← hjEq]
      unfold sourceIndex
      congr 1
      omega
    exact (hiso.2 (ip1 + b) hne hs hc).elim
  by_cases hjFar : j < F.near.length + ((P.drop ip1).take (ip2 - ip1)).length + F.far.length
  · have hnu : nu = mu := label_eq_of_isCompOf hletter
      (F.far_labels _ (getElem_mem_fourGon_r _ _ _ _ (by omega) hjFar hjlt))
    subst nu
    have hjEq : j = F.near.length + ((P.drop ip1).take (ip2 - ip1)).length := by
      have hlen := F.far_length
      omega
    have hc := F.connected_source_of_far (by omega) hip2 haLe (by rw [← hjEq]; exact hconn)
    rw [ha] at hc
    have hs : Connected D.fam mu vp P (ip2 - 1) ip2 :=
      span_mem_fam_of_isComp D vp hletP hfar
    have hc' := connected_trans hc (connected_symm hs)
    exact (hiso.2 (ip2 - 1) (by omega) ⟨ip2, hfar⟩ hc').elim
  let b := ((Q.drop iq1).take (iq2 - iq1)).length -
    (j - (F.near.length + ((P.drop ip1).take (ip2 - ip1)).length + F.far.length))
  have hjBound : j < F.near.length + ((P.drop ip1).take (ip2 - ip1)).length +
      F.far.length + ((Q.drop iq1).take (iq2 - iq1)).length := by
    change j < (F.near ++ (P.drop ip1).take (ip2 - ip1) ++ F.far ++
      revWord ((Q.drop iq1).take (iq2 - iq1))).length at hjlt
    rwa [length_fourGon] at hjlt
  have hb : b ≤ ((Q.drop iq1).take (iq2 - iq1)).length := by dsimp [b]; omega
  have hb0 : 0 < b := by dsimp [b]; omega
  have hjEq : F.targetIndex b = j := by dsimp [targetIndex, b]; omega
  have hs : IsCompStart nu
      (F.near ++ (P.drop ip1).take (ip2 - ip1) ++ F.far ++
        revWord ((Q.drop iq1).take (iq2 - iq1)))
      (F.near.length + ((P.drop ip1).take (ip2 - ip1)).length + F.far.length +
        (((Q.drop iq1).take (iq2 - iq1)).length - b)) := by
    rw [← hjEq] at hstart
    exact hstart
  obtain ⟨qstart, hqComp⟩ := exists_component_of_opposite_start_421 hb hb0 hs
  have hqOriginal := isComp_of_segment_of_isWThree hW3Q hqComp
  have hmatch := (F.cross_connection_iff haLe (by omega : b ≤ iq2 - iq1)).mp
    (by rw [hjEq]; exact hconn)
  rw [ha] at hmatch
  have hqSpan := span_mem_fam_of_isComp D vq hletQ hqOriginal
  refine ⟨iq1 + qstart, iq1 + b, hqOriginal, by omega, by omega, ?_⟩
  have hm := (D.fam nu).mul_mem hmatch ((D.fam nu).inv_mem hqSpan)
  convert hm using 1
  group

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.DGO421MinimalityFourGonData.exists_opposite_match
