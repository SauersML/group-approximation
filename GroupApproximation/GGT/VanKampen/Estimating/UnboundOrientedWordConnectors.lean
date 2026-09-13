import GroupApproximation.GGT.VanKampen.Estimating.UnboundMonotoneMorseIndex
import GroupApproximation.GGT.VanKampen.Estimating.UnboundWordConnectors
import GroupApproximation.Meta.AxiomGuard

/-!
# Oriented connector words for the unbound-polygon pair

Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, arXiv:math/0411039v3, Appendix, proof of Lemma 9.4, Case 1.
`WordConnectorPair` reads its source segment forwards (`a < a'`) and allows either
direction on the target segment.  Planar surgery contradicts only the antiparallel
case `b' < b`.  There the boundary loop
`source[a, a'] · endConnector · target[b', b] · startConnector` reads both original
segments forwards, as the polygon does.

* `OrientedWordConnectorPair` extends `WordConnectorPair` by `target_backward : b' < b`.
* `OrientedWordSidePair` is `WordSidePair` with `a < a'` and `b' < b`;
  `OrientedWordSidePair.exists_connectors` builds the connector words.
* `OsinUnboundScale.orientedWordSidePair_of_parameters` moves an antiparallel pair of
  long segments on two sides of the geodesic replacement polygon to original vertex
  indices and keeps the orientation.  Morse proximity supplies the indices, and the
  monotone index choice (`index_lt_of_prefix_near`) orders them, since the segment
  length of the scale exceeds `3 kappa + 6 δ` (`OsinUnboundScale.morse_gap_lt`).
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

section Connectors

open GroupApproximation.HullSC OsinComponents

/-- The actual connector pair in the antiparallel configuration: the source segment
runs forwards from `a` to `a'`, the target segment backwards from `b` to `b'`. -/
structure OrientedWordConnectorPair (D : RelGenSet G Lambda) (v : ℕ → G)
    (word : ℕ → List (RelLetter G Lambda)) (n : ℕ) (A B : Set ℕ) (eps : ℕ)
    extends WordConnectorPair D v word n A B eps where
  target_backward : b' < b

namespace OrientedWordConnectorPair

variable {D : RelGenSet G Lambda} {v : ℕ → G}
  {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}
  (C : OrientedWordConnectorPair D v word n A B eps)

/-- The target word of an oriented pair is the original run from `b'` to `b`, read
backwards. -/
theorem targetWord_eq : C.toWordConnectorPair.targetWord =
    RelWord.revInv (((word C.target).drop C.b').take (C.b - C.b')) := by
  simp only [WordConnectorPair.targetWord, orientedWordSegment,
    if_neg (Nat.not_le.mpr C.target_backward)]

end OrientedWordConnectorPair

/-- Two distinct original word sides with short cross-connectors and long segments,
in the antiparallel configuration `a < a'` and `b' < b`. -/
def OrientedWordSidePair (D : RelGenSet G Lambda) (v : ℕ → G)
    (word : ℕ → List (RelLetter G Lambda)) (n : ℕ) (A B : Set ℕ) (eps : ℕ) : Prop :=
  ∃ i < n, ∃ j < n, i ∈ A ∧ j ∈ B ∧ i ≠ j ∧
    ∃ a ≤ (word i).length, ∃ a' ≤ (word i).length,
      ∃ b ≤ (word j).length, ∃ b' ≤ (word j).length,
        a < a' ∧ b' < b ∧
        wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a)
          (OsinComponents.vertex (v j) (word j) b) < eps ∧
        wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a')
          (OsinComponents.vertex (v j) (word j) b') < eps ∧
        eps < wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a)
          (OsinComponents.vertex (v i) (word i) a') ∧
        eps < wordDist D.alphabet.carrier (OsinComponents.vertex (v j) (word j) b)
          (OsinComponents.vertex (v j) (word j) b')

/-- An oriented pair is in particular a pair. -/
theorem OrientedWordSidePair.toWordSidePair {D : RelGenSet G Lambda} {v : ℕ → G}
    {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}
    (hpair : OrientedWordSidePair D v word n A B eps) :
    WordSidePair D v word n A B eps := by
  obtain ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb', -, -,
    hcross, hcross', hlong, hlong'⟩ := hpair
  exact ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb',
    hcross, hcross', hlong, hlong'⟩

/-- The oriented metric pair constructs an oriented pair of actual relative connector
words.  No swap is needed: the pair already has `a < a'` and `b' < b`. -/
theorem OrientedWordSidePair.exists_connectors
    {D : RelGenSet G Lambda} {v : ℕ → G}
    {word : ℕ → List (RelLetter G Lambda)} {n eps : ℕ} {A B : Set ℕ}
    (hpair : OrientedWordSidePair D v word n A B eps)
    (hletters : ∀ i < n, i ∈ A ∨ i ∈ B → RelWord.IsAdmissible D (word i)) :
    Nonempty (OrientedWordConnectorPair D v word n A B eps) := by
  obtain ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb', haa', hbb',
    hcross, hcross', hlong, hlong'⟩ := hpair
  obtain ⟨s, hs⟩ := existsGeodesicWord D (OsinComponents.vertex (v j) (word j) b)
    (OsinComponents.vertex (v i) (word i) a)
  obtain ⟨t, ht⟩ := existsGeodesicWord D (OsinComponents.vertex (v i) (word i) a')
    (OsinComponents.vertex (v j) (word j) b')
  exact ⟨{
    source := i, target := j, source_lt := hi, target_lt := hj
    source_mem := hiA, target_mem := hjB, distinct := hne
    source_admissible := hletters i hi (Or.inl hiA)
    target_admissible := hletters j hj (Or.inr hjB)
    a := a, a' := a', b := b, b' := b'
    a_le := ha, a'_le := ha', b_le := hb, b'_le := hb', source_forward := haa'
    source_long := hlong, target_long := hlong'
    startConnector := s, endConnector := t, start_geodesic := hs, end_geodesic := ht
    start_short := by
      simpa only [hs.2.2, wordDist_comm D.alphabet.symmetricGenerating] using hcross
    end_short := by simpa only [ht.2.2] using hcross'
    target_backward := hbb' }⟩

end Connectors

section Transfer

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel

/-- **Oriented transfer to original vertices.**  Take the geodesic replacement polygon
of a cyclic word polygon in a `δ`-hyperbolic Cayley realisation, a Morse radius
`kappa` for the retained classes, and an antiparallel pair of long segments on a
side `i ∈ A` and a side `j ∈ B`: `side i` runs from `u` to `u'` and `side j` from
`t` to `t'` backwards, both at least the segment length of the scale, with matched
endpoints within `12 (δ + 1)`.  Then the original words carry an oriented word pair
at `eps`. -/
theorem OsinUnboundScale.orientedWordSidePair_of_parameters
    {D : RelGenSet G Lambda} {δ lambda c mu kappa : ℝ} {eps rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * (δ + 1)) (100000 * (δ + 1)) eps rho)
    (hδ : IsHyperbolicSpace δ (PointQuot D.alphabet)) (hδ0 : 0 ≤ δ)
    (hmorse : IsWordMorseRadius D lambda c kappa)
    {n : ℕ} {v : ℕ → G} {word : ℕ → List (RelLetter G Lambda)}
    {sides : ℕ → ℝ → PointQuot D.alphabet}
    (hpoly : IsClosedPolygonAt (fun i => vertexQuot D.alphabet (v i)) sides 0 n)
    (hends : ∀ i < n, v (i + 1) = v i * RelLetter.listVal (word i)) (A B : Set ℕ)
    (hquasi : ∀ i < n, i ∈ A ∨ i ∈ B → IsLambdaCQuasiGeodesicWord D lambda c (word i))
    {i j : ℕ} (hi : i < n) (hj : j < n) (hiA : i ∈ A) (hjB : j ∈ B) (hne : i ≠ j)
    {u u' t t' : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ)
      (dist (vertexQuot D.alphabet (v i)) (vertexQuot D.alphabet (v (i + 1)))))
    (hu' : u' ∈ Set.Icc (0 : ℝ)
      (dist (vertexQuot D.alphabet (v i)) (vertexQuot D.alphabet (v (i + 1)))))
    (ht : t ∈ Set.Icc (0 : ℝ)
      (dist (vertexQuot D.alphabet (v j)) (vertexQuot D.alphabet (v (j + 1)))))
    (ht' : t' ∈ Set.Icc (0 : ℝ)
      (dist (vertexQuot D.alphabet (v j)) (vertexQuot D.alphabet (v (j + 1)))))
    (hlen : (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 ≤ u' - u)
    (hlen' : (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 ≤ t - t')
    (hc : dist (sides i u) (sides j t) ≤ 12 * (δ + 1))
    (hc' : dist (sides i u') (sides j t') ≤ 12 * (δ + 1)) :
    OrientedWordSidePair D v word n A B eps := by
  have hnear : ∀ k < n, k ∈ A ∨ k ∈ B →
      ∀ r ∈ Set.Icc (0 : ℝ)
        (dist (vertexQuot D.alphabet (v k)) (vertexQuot D.alphabet (v (k + 1)))),
      ∃ m ≤ (word k).length, dist (sides k r)
        (vertexQuot D.alphabet (OsinComponents.vertex (v k) (word k) m)) ≤ kappa := by
    intro k hk hkAB r hr
    obtain ⟨hgeo, hz, he⟩ := hpoly.1 k (Nat.zero_le k) (by simpa using hk)
    have hgeo' : IsGeodesicSegment (sides k) 0
        (dist (vertexQuot D.alphabet (v k))
          (vertexQuot D.alphabet (v k * RelLetter.listVal (word k)))) := by
      simpa only [hends k hk] using hgeo
    have he' : sides k (dist (vertexQuot D.alphabet (v k))
        (vertexQuot D.alphabet (v k * RelLetter.listVal (word k)))) =
      vertexQuot D.alphabet (v k * RelLetter.listVal (word k)) := by
      simpa only [hends k hk] using he
    have hr' : r ∈ Set.Icc (0 : ℝ)
        (dist (vertexQuot D.alphabet (v k))
          (vertexQuot D.alphabet (v k * RelLetter.listVal (word k)))) := by
      simpa only [hends k hk] using hr
    exact (hmorse (word k) (hquasi k hk hkAB) (v k) (sides k) hgeo' hz he').2 r hr'
  obtain ⟨a, ha, hpa⟩ := hnear i hi (Or.inl hiA) u hu
  obtain ⟨a', ha', hpa'⟩ := hnear i hi (Or.inl hiA) u' hu'
  obtain ⟨b, hb, hqb⟩ := hnear j hj (Or.inr hjB) t ht
  obtain ⟨b', hb', hqb'⟩ := hnear j hj (Or.inr hjB) t' ht'
  have hgap := scale.morse_gap_lt (le_trans dist_nonneg hpa) hδ0
  obtain ⟨hgi, hzi, -⟩ := hpoly.1 i (Nat.zero_le i) (by simpa using hi)
  obtain ⟨hgj, hzj, -⟩ := hpoly.1 j (Nat.zero_le j) (by simpa using hj)
  have haa' : a < a' := index_lt_of_prefix_near hδ hδ0 hmorse (hquasi i hi (Or.inl hiA))
    hgi hzi hu hu' ha hpa hpa' (by linarith)
  have hbb' : b' < b := index_lt_of_prefix_near hδ hδ0 hmorse (hquasi j hj (Or.inr hjB))
    hgj hzj ht' ht hb' hqb' hqb (by linarith)
  have hlenI : (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 ≤
      dist (sides i u) (sides i u') := by
    rw [hgi u hu u' hu', abs_sub_comm]
    exact le_trans hlen (le_abs_self _)
  have hlenJ : (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 ≤
      dist (sides j t) (sides j t') := by
    rw [hgj t ht t' ht']
    exact le_trans hlen' (le_abs_self _)
  obtain ⟨hcross, hcross', hlong, hlong'⟩ := nearby_endpoints_keep_shortening_margin
    hlenI hlenJ hc hc' hpa hpa' hqb hqb' scale.epsilon_large scale.shortcut_shortens
  refine ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb', haa', hbb',
    ?_, ?_, ?_, ?_⟩
  · simpa only [dist_vertexQuot, Nat.cast_lt] using hcross
  · simpa only [dist_vertexQuot, Nat.cast_lt] using hcross'
  · simpa only [dist_vertexQuot, Nat.cast_lt] using hlong
  · simpa only [dist_vertexQuot, Nat.cast_lt] using hlong'

end Transfer

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OrientedWordConnectorPair.targetWord_eq
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OrientedWordSidePair.toWordSidePair
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OrientedWordSidePair.exists_connectors
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OsinUnboundScale.orientedWordSidePair_of_parameters
