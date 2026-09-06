import GroupApproximation.GGT.DGOLemma421MinimalityInterior

/-!
# Rank gaps between matched W-word components

The word conditions supply the isolation and relative depth needed by the
minimality quadrilateral. An intermediate source rank then forces an
intermediate target rank. This is the geometric step in DGO's minimal-gap
argument, with the two path basepoints retained throughout.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The span of an occurrence is its written peripheral element, so (W2)
gives its depth at every path basepoint. -/
theorem PeripheralOccurrence.span_not_mem_relBall
    {D : RelGenSet G Lambda} {word : List (RelLetter G Lambda)} {R : ℕ}
    (hW2 : WWord.IsWTwo D R word) (v : G) (A : PeripheralOccurrence word) :
    (vertex v word A.pos)⁻¹ * vertex v word (A.pos + 1) ∉ D.relBall A.label R := by
  rw [vertex_succ word v A.pos (List.getElem?_eq_some_iff.mp A.read).1,
    inv_mul_cancel_left, (List.getElem?_eq_some_iff.mp A.read).2]
  exact hW2 A.pos A.label A.value A.read

/-- Isolation applies to any component start, independently of its chosen
canonical rank. -/
theorem isIsolated_of_isCompStart_of_uniformBound
    {D : RelGenSet G Lambda} {C : ℕ} (hC : 0 < C)
    (hbound : DGOUniformSumBound D 1 1 C)
    {word : List (RelLetter G Lambda)}
    (hlet : ∀ letter ∈ word, D.IsLetter letter)
    (hW1 : WWord.IsWOne word) (hW2 : WWord.IsWTwo D (50 * C) word)
    (hW3 : WWord.IsWThree D word) (v : G) {nu : Lambda} {i : ℕ}
    (hstart : IsCompStart nu word i) : IsIsolated D.fam nu v word i := by
  obtain ⟨r, hrpos, hrlabel⟩ := exists_peripheralOccurrence_eq_of_isCompStart hstart
  have h := peripheralOccurrence_isIsolated_of_uniformBound hC hbound hlet hW1 hW2 hW3 v r
  rwa [hrpos, hrlabel] at h

/-- Moving both matched starts to their component ends preserves the coset
match. This gives the far connector of the minimality quadrilateral. -/
theorem cosetMatch_ends_of_starts
    {D : RelGenSet G Lambda} {P Q : List (RelLetter G Lambda)} {vp vq : G}
    {nu : Lambda} {i k j l : ℕ}
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hP : IsComp nu P i k) (hQ : IsComp nu Q j l)
    (hmatch : (vertex vp P i)⁻¹ * vertex vq Q j ∈ D.fam nu) :
    (vertex vp P k)⁻¹ * vertex vq Q l ∈ D.fam nu := by
  have hm := (D.fam nu).mul_mem
    ((D.fam nu).mul_mem ((D.fam nu).inv_mem (span_mem_fam_of_isComp D vp hletP hP))
      hmatch) (span_mem_fam_of_isComp D vq hletQ hQ)
  convert hm using 1
  group

omit [Group G] in
/-- Canonical rank order can be recovered from strict position order. -/
theorem peripheralOccurrence_rank_lt_of_pos_lt
    (word : List (RelLetter G Lambda)) {s t : Fin (peripheralPositions word).card}
    (hpos : (peripheralOccurrence word s).pos < (peripheralOccurrence word t).pos) :
    s < t := by
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exact hlt
  · subst t
    omega
  · have := peripheralOccurrence_pos_lt word hgt
    omega


/-- Any source rank strictly between two forward matched pairs has a match
strictly between the two target ranks. Isolation and depth are consequences
of (W1)--(W3) at the displayed uniform threshold. -/
theorem exists_intermediate_rank_match_of_uniformBounds
    {D : RelGenSet G Lambda} {C11 C414 : ℕ} (hC11 : 0 < C11)
    (hbound : DGOUniformSumBound D 1 1 C11)
    (hproj : ∀ (n : ℕ) (v : G) (word : List (RelLetter G Lambda)),
      IsQuasiGeodesicPolygon D 4 1 n v word →
      ∀ (nu : Lambda) (i k : ℕ), IsComp nu word i k → IsIsolated D.fam nu v word i →
        (vertex v word i)⁻¹ * vertex v word k ∈ D.relBall nu (C414 * n))
    (hbase : DGO421BaseSymmetric D)
    {P Q : List (RelLetter G Lambda)} {vp vq : G}
    (hletP : ∀ letter ∈ P, D.IsLetter letter) (hletQ : ∀ letter ∈ Q, D.IsLetter letter)
    (hW1P : WWord.IsWOne P)
    (hW2P : WWord.IsWTwo D (max (50 * C11) (C414 * 4)) P)
    (hW3P : WWord.IsWThree D P) (hW3Q : WWord.IsWThree D Q)
    (hqgP : ∀ i j : ℕ, i ≤ j → j ≤ P.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vp P i) (vertex vp P j) : ℝ))
    (hqgQ : ∀ i j : ℕ, i ≤ j → j ≤ Q.length →
      ((j - i : ℕ) : ℝ) / 4 - 1 ≤
        (wordDist D.alphabet.carrier (vertex vq Q i) (vertex vq Q j) : ℝ))
    {s r t : Fin (peripheralPositions P).card}
    {a b : Fin (peripheralPositions Q).card}
    (hsr : s < r) (hrt : r < t) (hab : a < b)
    (hlabelA : (peripheralOccurrence Q a).label = (peripheralOccurrence P s).label)
    (hlabelB : (peripheralOccurrence Q b).label = (peripheralOccurrence P t).label)
    (hmatchA : (vertex vp P (peripheralOccurrence P s).pos)⁻¹ *
      vertex vq Q (peripheralOccurrence Q a).pos ∈ D.fam (peripheralOccurrence P s).label)
    (hmatchB : (vertex vp P (peripheralOccurrence P t).pos)⁻¹ *
      vertex vq Q (peripheralOccurrence Q b).pos ∈ D.fam (peripheralOccurrence P t).label) :
    ∃ c : Fin (peripheralPositions Q).card, a < c ∧ c < b ∧
      (peripheralOccurrence Q c).label = (peripheralOccurrence P r).label ∧
      (vertex vp P (peripheralOccurrence P r).pos)⁻¹ *
        vertex vq Q (peripheralOccurrence Q c).pos ∈ D.fam (peripheralOccurrence P r).label := by
  have hs := PeripheralOccurrence.isComp hW3P s
  have hr := PeripheralOccurrence.isComp hW3P r
  have ht := PeripheralOccurrence.isComp hW3P t
  have ha := PeripheralOccurrence.isComp hW3Q a
  have hb := PeripheralOccurrence.isComp hW3Q b
  rw [hlabelA] at ha
  rw [hlabelB] at hb
  have hsrpos := peripheralOccurrence_pos_lt P hsr
  have hrtpos := peripheralOccurrence_pos_lt P hrt
  have habpos := peripheralOccurrence_pos_lt Q hab
  have hfarMatch := cosetMatch_ends_of_starts hletP hletQ ht hb hmatchB
  obtain ⟨F⟩ := exists_minimalityFourGon_at D hbase hletP hletQ hmatchA hfarMatch
    (by omega) (by omega) ht.2.1 hb.2.1 hqgP hqgQ
  have hW2iso : WWord.IsWTwo D (50 * C11) P := by
    intro i nu g hread hmem
    exact hW2P i nu g hread (relBall_mono_radius D nu (Nat.le_max_left _ _) hmem)
  have hiso := peripheralOccurrence_isIsolated_of_uniformBound hC11 hbound hletP
    hW1P hW2iso hW3P vp r
  have hdeep : (vertex vp P (peripheralOccurrence P r).pos)⁻¹ *
      vertex vp P ((peripheralOccurrence P r).pos + 1) ∉
        D.relBall (peripheralOccurrence P r).label (C414 * 4) := by
    intro hmem
    exact PeripheralOccurrence.span_not_mem_relBall hW2P vp (peripheralOccurrence P r)
      (relBall_mono_radius D _ (Nat.le_max_right _ _) hmem)
  have ht' : IsComp (peripheralOccurrence P t).label P
      ((peripheralOccurrence P t).pos + 1 - 1) ((peripheralOccurrence P t).pos + 1) := by
    simpa using ht
  have hb' : IsComp (peripheralOccurrence P t).label Q
      ((peripheralOccurrence Q b).pos + 1 - 1) ((peripheralOccurrence Q b).pos + 1) := by
    simpa using hb
  obtain ⟨j, k, hcomp, hj, hk, hmatch⟩ := F.exists_internal_opposite_match hproj hletP hletQ
    hW3P hW3Q hs ht' ha hb' hr hiso hsrpos (by omega) ht.2.1 (by omega) hb.2.1 hdeep
  obtain ⟨c, hcpos, hclabel⟩ := exists_peripheralOccurrence_eq_of_isCompStart ⟨k, hcomp⟩
  refine ⟨c, peripheralOccurrence_rank_lt_of_pos_lt Q (by rwa [hcpos]), ?_, hclabel, ?_⟩
  · apply peripheralOccurrence_rank_lt_of_pos_lt Q
    rw [hcpos]
    have := isComp_succ_of_isWThree hW3Q hcomp
    omega
  · rwa [hcpos]

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.PeripheralOccurrence.span_not_mem_relBall
#audit_axioms GroupApproximation.GGT.OsinComponents.isIsolated_of_isCompStart_of_uniformBound
#audit_axioms GroupApproximation.GGT.OsinComponents.cosetMatch_ends_of_starts
#audit_axioms GroupApproximation.GGT.OsinComponents.peripheralOccurrence_rank_lt_of_pos_lt

#audit_axioms GroupApproximation.GGT.OsinComponents.exists_intermediate_rank_match_of_uniformBounds
