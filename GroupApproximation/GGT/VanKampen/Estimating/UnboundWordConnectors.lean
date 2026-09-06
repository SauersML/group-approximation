import GroupApproximation.GGT.VanKampen.Estimating.UnboundWordPolygon
import GroupApproximation.GGT.VanKampen.WordSegmentConnectors

/-!
# Actual connector words for the unbound-polygon pair

The first side is read forwards in its original word. The second side can
be read in either direction, with the two connectors retaining their matched
endpoints. Their quadrilateral label is trivial in the ambient group, and
the beginning of the target word admits a strict shortening to the source
side. These are word-level constructions; no embedded contiguity region or
replacement cutting-path system is asserted here.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.WordMetric GroupApproximation.HullSC OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- The two actual original subsegments and geodesic connector words. -/
structure WordConnectorPair (D : RelGenSet G Lambda) (v : ℕ → G)
    (word : ℕ → List (RelLetter G Lambda)) (n : ℕ) (A B : Set ℕ) (eps : ℕ) where
  source : ℕ
  target : ℕ
  source_lt : source < n
  target_lt : target < n
  source_mem : source ∈ A
  target_mem : target ∈ B
  distinct : source ≠ target
  source_admissible : RelWord.IsAdmissible D (word source)
  target_admissible : RelWord.IsAdmissible D (word target)
  a : ℕ
  a' : ℕ
  b : ℕ
  b' : ℕ
  a_le : a ≤ (word source).length
  a'_le : a' ≤ (word source).length
  b_le : b ≤ (word target).length
  b'_le : b' ≤ (word target).length
  source_forward : a < a'
  source_long : eps < wordDist D.alphabet.carrier
    (vertex (v source) (word source) a) (vertex (v source) (word source) a')
  target_long : eps < wordDist D.alphabet.carrier
    (vertex (v target) (word target) b) (vertex (v target) (word target) b')
  startConnector : List (RelLetter G Lambda)
  endConnector : List (RelLetter G Lambda)
  start_geodesic : IsGeodesicWord D
    (vertex (v target) (word target) b) (vertex (v source) (word source) a) startConnector
  end_geodesic : IsGeodesicWord D
    (vertex (v source) (word source) a') (vertex (v target) (word target) b') endConnector
  start_short : startConnector.length < eps
  end_short : endConnector.length < eps

/-- The metric pair constructs a pair of actual relative connector words.
Swapping both matched endpoint pairs makes the source segment forward. -/
theorem WordSidePair.exists_connectors
    {D : RelGenSet G Lambda} {v : ℕ → G}
    {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}
    (hpair : WordSidePair D v word n A B eps)
    (hletters : ∀ i < n, i ∈ A ∨ i ∈ B → RelWord.IsAdmissible D (word i)) :
    Nonempty (WordConnectorPair D v word n A B eps) := by
  obtain ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb', hcross,
    hcross', hlong, hlong'⟩ := hpair
  have build (a a' b b' : ℕ) (ha : a ≤ (word i).length) (ha' : a' ≤ (word i).length)
      (hb : b ≤ (word j).length) (hb' : b' ≤ (word j).length) (haa' : a < a')
      (hc : wordDist D.alphabet.carrier (vertex (v i) (word i) a)
        (vertex (v j) (word j) b) < eps)
      (hc' : wordDist D.alphabet.carrier (vertex (v i) (word i) a')
        (vertex (v j) (word j) b') < eps)
      (hl : eps < wordDist D.alphabet.carrier (vertex (v i) (word i) a)
        (vertex (v i) (word i) a'))
      (hl' : eps < wordDist D.alphabet.carrier (vertex (v j) (word j) b)
        (vertex (v j) (word j) b')) :
      Nonempty (WordConnectorPair D v word n A B eps) := by
    obtain ⟨s, hs⟩ := existsGeodesicWord D (vertex (v j) (word j) b)
      (vertex (v i) (word i) a)
    obtain ⟨t, ht⟩ := existsGeodesicWord D (vertex (v i) (word i) a')
      (vertex (v j) (word j) b')
    exact ⟨{
      source := i, target := j, source_lt := hi, target_lt := hj
      source_mem := hiA, target_mem := hjB, distinct := hne
      source_admissible := hletters i hi (Or.inl hiA)
      target_admissible := hletters j hj (Or.inr hjB)
      a := a, a' := a', b := b, b' := b'
      a_le := ha, a'_le := ha', b_le := hb, b'_le := hb', source_forward := haa'
      source_long := hl, target_long := hl'
      startConnector := s, endConnector := t, start_geodesic := hs, end_geodesic := ht
      start_short := by simpa only [hs.2.2, wordDist_comm D.alphabet.symmetricGenerating] using hc
      end_short := by simpa only [ht.2.2] using hc' }⟩
  rcases lt_trichotomy a a' with haa' | haa' | haa'
  · exact build a a' b b' ha ha' hb hb' haa' hcross hcross' hlong hlong'
  · subst a'
    simp only [wordDist_self, Nat.not_lt_zero] at hlong
  · apply build a' a b' b ha' ha hb' hb haa' hcross' hcross
    · rwa [wordDist_comm D.alphabet.symmetricGenerating]
    · rwa [wordDist_comm D.alphabet.symmetricGenerating]

namespace WordConnectorPair

variable {D : RelGenSet G Lambda} {v : ℕ → G}
  {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}
  (C : WordConnectorPair D v word n A B eps)

def sourceWord : List (RelLetter G Lambda) :=
  orientedWordSegment (word C.source) C.a C.a'

def targetWord : List (RelLetter G Lambda) :=
  orientedWordSegment (word C.target) C.b C.b'

theorem sourceWord_eq : C.sourceWord = ((word C.source).drop C.a).take (C.a' - C.a) := by
  simp only [sourceWord, orientedWordSegment, if_pos C.source_forward.le]

def boundaryWord : List (RelLetter G Lambda) :=
  C.sourceWord ++ C.endConnector ++ RelWord.revInv C.targetWord ++ C.startConnector

/-- The actual four words form an ambient-group null loop. -/
theorem boundaryWord_value : RelLetter.listVal C.boundaryWord = 1 := by
  have hq1 := orientedWordSegment_transport (word C.source) (v C.source) C.a C.a'
  have hq2 := orientedWordSegment_transport (word C.target) (v C.target) C.b C.b'
  change vertex (v C.source) (word C.source) C.a * RelLetter.listVal C.sourceWord = _ at hq1
  change vertex (v C.target) (word C.target) C.b * RelLetter.listVal C.targetWord = _ at hq2
  apply mul_left_cancel (a := vertex (v C.source) (word C.source) C.a)
  rw [mul_one, boundaryWord, RelWord.listVal_append, RelWord.listVal_append,
    RelWord.listVal_append, RelWord.listVal_revInv]
  calc
    _ = ((vertex (v C.source) (word C.source) C.a * RelLetter.listVal C.sourceWord) *
        RelLetter.listVal C.endConnector) * (RelLetter.listVal C.targetWord)⁻¹ *
        RelLetter.listVal C.startConnector := by group
    _ = vertex (v C.target) (word C.target) C.b' * (RelLetter.listVal C.targetWord)⁻¹ *
        RelLetter.listVal C.startConnector := by rw [hq1, C.end_geodesic.2.1]
    _ = vertex (v C.target) (word C.target) C.b * RelLetter.listVal C.startConnector := by
      rw [← hq2]
      group
    _ = _ := C.start_geodesic.2.1

theorem segment_lengths (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    eps < C.sourceWord.length ∧ eps < C.targetWord.length :=
  ⟨lt_of_lt_of_le C.source_long
      (wordDist_le_orientedWordSegment_length hsymm C.source_admissible _ _ _),
    lt_of_lt_of_le C.target_long
      (wordDist_le_orientedWordSegment_length hsymm C.target_admissible _ _ _)⟩

theorem boundaryWord_admissible (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    RelWord.IsAdmissible D C.boundaryWord := by
  have hq1 := orientedWordSegment_admissible hsymm C.source_admissible C.a C.a'
  have hq2 := isAdmissible_revInv hsymm
    (orientedWordSegment_admissible hsymm C.target_admissible C.b C.b')
  intro x hx
  simp only [boundaryWord, List.mem_append] at hx
  rcases hx with ((hx | hx) | hx) | hx
  · exact hq1 x hx
  · exact C.end_geodesic.1 x hx
  · exact hq2 x hx
  · exact C.start_geodesic.1 x hx

/-- Independently of target orientation, its original prefix has a shorter
continuation to one of the actual source endpoints. -/
theorem exists_shorter_target_prefix :
    ∃ k : ℕ, (k = C.a ∨ k = C.a') ∧
      ∃ s : List (RelLetter G Lambda),
        IsGeodesicWord D (vertex (v C.target) (word C.target) (min C.b C.b'))
          (vertex (v C.source) (word C.source) k) s ∧ s.length < eps ∧
        RelWord.IsAdmissible D ((word C.target).take (min C.b C.b') ++ s) ∧
        v C.target * RelLetter.listVal ((word C.target).take (min C.b C.b') ++ s) =
          vertex (v C.source) (word C.source) k ∧
        ((word C.target).take (min C.b C.b') ++ s).length < (word C.target).length := by
  by_cases hbb' : C.b ≤ C.b'
  · refine ⟨C.a, Or.inl rfl, ?_⟩
    rw [min_eq_left hbb']
    apply exists_shorter_prefix_connector D C.target_admissible _ _ hbb' C.b'_le C.target_long
    simpa only [← C.start_geodesic.2.2] using C.start_short
  · have hb'b : C.b' ≤ C.b := by omega
    refine ⟨C.a', Or.inr rfl, ?_⟩
    rw [min_eq_right hb'b]
    apply exists_shorter_prefix_connector D C.target_admissible _ _ hb'b C.b_le
    · rw [wordDist_comm D.alphabet.symmetricGenerating]
      exact C.target_long
    · rw [wordDist_comm D.alphabet.symmetricGenerating, ← C.end_geodesic.2.2]
      exact C.end_short

end WordConnectorPair
end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordSidePair.exists_connectors
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair.boundaryWord_value
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair.segment_lengths
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair.boundaryWord_admissible
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.WordConnectorPair.exists_shorter_target_prefix
