import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94AntiparallelMetric
import GroupApproximation.Meta.AxiomGuard

/-!
# The metric half of Osin's Lemma 9.4 at two thresholds

Osin, arXiv:math/0411039v3, Appendix, proof of Lemma 9.4.  `osinLemma94AntiparallelMetric` gives a
backwards connector pair at one threshold `ε`: connectors shorter than `ε`, segments longer than `ε`.
The two bounds come from different parts of the argument.  The connectors are short because matched
endpoints of the geodesic replacement polygon are `12 (δ + 1)` apart and every original vertex lies
within a Morse radius `κ`, so they are shorter than any `εC` above `12 (δ + 1) + 2 κ`.  The segments
are long because the density margin of the scale exceeds its `ε` (`OsinUnboundScale.shortcut_shortens`).
So one pair carries connectors below `εC` and segments above any `εL ≥ εC` at once, by reading
`nearby_endpoints_keep_shortening_margin` at `εC` and at `εL`.

Consumer: the gap corners of class words.  Moving an endpoint strictly inside a gap to a corner moves it
by at most half a gap, so a pair with connectors below `ε − B` and segments above `ε + B` gives a pair
at `ε` with no gap endpoint, where `B = ⌈(c + 2) / λ⌉₊` bounds the gaps.

* `UnboundEstimate.OrientedWordSidePairTwo`, `OrientedWordSidePairTwo.exists_connectors`.
* `UnboundEstimate.OsinUnboundScale.orientedWordSidePairTwo_of_parameters`,
  `orientedWordSidePairTwo_of_orientedClassPair`.
* `UnboundEstimate.unboundOrientedWordPolygonMonotoneTwo`.
* `OsinLemma94DensePolygonsAntiparallelTwo`, `osinLemma94AntiparallelMetricTwo`.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 9.4 inside the proof of Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel
open GroupApproximation.HullSC OsinComponents

universe u w v

section Pairs

variable {G : Type u} [Group G] {Lambda : Type w}

/-- Two distinct original word sides with cross-connectors shorter than `epsC` and segments longer
than `epsL`, in the antiparallel configuration `a < a'` and `b' < b`. -/
def OrientedWordSidePairTwo (D : RelGenSet G Lambda) (v : ℕ → G)
    (word : ℕ → List (RelLetter G Lambda)) (n : ℕ) (A B : Set ℕ) (epsC epsL : ℕ) : Prop :=
  ∃ i < n, ∃ j < n, i ∈ A ∧ j ∈ B ∧ i ≠ j ∧
    ∃ a ≤ (word i).length, ∃ a' ≤ (word i).length,
      ∃ b ≤ (word j).length, ∃ b' ≤ (word j).length,
        a < a' ∧ b' < b ∧
        wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a)
          (OsinComponents.vertex (v j) (word j) b) < epsC ∧
        wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a')
          (OsinComponents.vertex (v j) (word j) b') < epsC ∧
        epsL < wordDist D.alphabet.carrier (OsinComponents.vertex (v i) (word i) a)
          (OsinComponents.vertex (v i) (word i) a') ∧
        epsL < wordDist D.alphabet.carrier (OsinComponents.vertex (v j) (word j) b)
          (OsinComponents.vertex (v j) (word j) b')

/-- **Connector words at `epsC`, keeping the segments above `epsL`.** -/
theorem OrientedWordSidePairTwo.exists_connectors
    {D : RelGenSet G Lambda} {v : ℕ → G}
    {word : ℕ → List (RelLetter G Lambda)} {n epsC epsL : ℕ} {A B : Set ℕ}
    (hpair : OrientedWordSidePairTwo D v word n A B epsC epsL) (hle : epsC ≤ epsL)
    (hletters : ∀ i < n, i ∈ A ∨ i ∈ B → RelWord.IsAdmissible D (word i)) :
    ∃ C : OrientedWordConnectorPair D v word n A B epsC,
      epsL < wordDist D.alphabet.carrier
          (OsinComponents.vertex (v C.source) (word C.source) C.a)
          (OsinComponents.vertex (v C.source) (word C.source) C.a') ∧
        epsL < wordDist D.alphabet.carrier
          (OsinComponents.vertex (v C.target) (word C.target) C.b)
          (OsinComponents.vertex (v C.target) (word C.target) C.b') := by
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
    source_long := lt_of_le_of_lt hle hlong, target_long := lt_of_le_of_lt hle hlong'
    startConnector := s, endConnector := t, start_geodesic := hs, end_geodesic := ht
    start_short := by
      simpa only [hs.2.2, wordDist_comm D.alphabet.symmetricGenerating] using hcross
    end_short := by simpa only [ht.2.2] using hcross'
    target_backward := hbb' }, hlong, hlong'⟩

/-- **Oriented transfer to original vertices, at two thresholds.**  As
`OsinUnboundScale.orientedWordSidePair_of_parameters`, with the scale at `epsL` and the closeness gate
at `epsC`. -/
theorem OsinUnboundScale.orientedWordSidePairTwo_of_parameters
    {D : RelGenSet G Lambda} {δ lambda c mu kappa : ℝ} {epsC epsL rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * (δ + 1)) (100000 * (δ + 1)) epsL rho)
    (hclose : 12 * (δ + 1) + 2 * kappa < (epsC : ℝ)) (hle : epsC ≤ epsL)
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
    OrientedWordSidePairTwo D v word n A B epsC epsL := by
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
  have hshortC : (epsC : ℝ) <
      (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 - 2 * kappa := by
    have h1 := scale.shortcut_shortens
    have h2 : (epsC : ℝ) ≤ (epsL : ℝ) := by exact_mod_cast hle
    linarith
  obtain ⟨hcross, hcross', -, -⟩ := nearby_endpoints_keep_shortening_margin
    hlenI hlenJ hc hc' hpa hpa' hqb hqb' hclose hshortC
  obtain ⟨-, -, hlong, hlong'⟩ := nearby_endpoints_keep_shortening_margin
    hlenI hlenJ hc hc' hpa hpa' hqb hqb' scale.epsilon_large scale.shortcut_shortens
  refine ⟨i, hi, j, hj, hiA, hjB, hne, a, ha, a', ha', b, hb, b', hb', haa', hbb',
    ?_, ?_, ?_, ?_⟩
  · simpa only [dist_vertexQuot, Nat.cast_lt] using hcross
  · simpa only [dist_vertexQuot, Nat.cast_lt] using hcross'
  · simpa only [dist_vertexQuot, Nat.cast_lt] using hlong
  · simpa only [dist_vertexQuot, Nat.cast_lt] using hlong'

/-- **Oriented class pair to original vertices, at two thresholds.** -/
theorem OsinUnboundScale.orientedWordSidePairTwo_of_orientedClassPair
    {D : RelGenSet G Lambda} {δ lambda c mu kappa : ℝ} {epsC epsL rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * (δ + 1)) (100000 * (δ + 1)) epsL rho)
    (hclose : 12 * (δ + 1) + 2 * kappa < (epsC : ℝ)) (hle : epsC ≤ epsL)
    (hδ : IsHyperbolicSpace δ (PointQuot D.alphabet)) (hδ0 : 0 ≤ δ)
    (hmorse : IsWordMorseRadius D lambda c kappa)
    {n : ℕ} {v : ℕ → G} {word : ℕ → List (RelLetter G Lambda)}
    {sides : ℕ → ℝ → PointQuot D.alphabet}
    (hpoly : IsClosedPolygonAt (fun i => vertexQuot D.alphabet (v i)) sides 0 n)
    (hends : ∀ i < n, v (i + 1) = v i * RelLetter.listVal (word i)) (A B : Set ℕ)
    (hquasi : ∀ i < n, i ∈ A ∨ i ∈ B → IsLambdaCQuasiGeodesicWord D lambda c (word i))
    (hpair : OrientedClassPair (fun i => vertexQuot D.alphabet (v i)) sides n A B
      ((lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000) (12 * (δ + 1))) :
    OrientedWordSidePairTwo D v word n A B epsC epsL := by
  obtain ⟨i, hi, j, hj, hiA, hjB, hne, u, hu, u', hu', t, ht, t', ht', hlen, hlen', hc, hc'⟩ :=
    hpair
  exact scale.orientedWordSidePairTwo_of_parameters hclose hle hδ hδ0 hmorse hpoly hends A B
    hquasi hi hj hiA hjB hne hu hu' ht' ht hlen hlen' hc hc'

end Pairs

/-- **The oriented metric part of Lemma 9.4 at two thresholds**: connectors below every `epsC` above
the closeness bound, segments above every `epsL ≥ epsC`, with a uniform `ρ` threshold for each pair of
thresholds. -/
def UnboundOrientedWordPolygonMonotoneTwoStatement : Prop :=
  ∀ (G : Type u) [Group G] (Lambda : Type w) (D : RelGenSet G Lambda)
    (δ lambda c mu : ℝ),
    IsHyperbolicSpace δ (Cayley D.alphabet) → 0 ≤ δ →
    0 < lambda → 0 ≤ c → 0 < mu →
    ∃ kappa : ℝ, 0 ≤ kappa ∧ ∃ eps0 : ℕ, ∀ epsC : ℕ, eps0 ≤ epsC → ∀ epsL : ℕ, epsC ≤ epsL →
      ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
        ∀ (n : ℕ) (v : ℕ → G) (word : ℕ → List (RelLetter G Lambda)) (A B : Set ℕ),
          v n = v 0 →
          (∀ i < n, v (i + 1) = v i * RelLetter.listVal (word i)) →
          (∀ i < n, i ∈ A ∨ i ∈ B → IsLambdaCQuasiGeodesicWord D lambda c (word i)) →
          (∀ i < n, i ∉ B → HullSC.RelWord.IsAdmissible D (word i) ∧ (word i).length ≤ epsL) →
          (n : ℝ) * Real.sqrt (rho : ℝ) / 240 < classWordLength word n A →
          OrientedWordSidePairTwo D v word n A B epsC epsL

theorem unboundOrientedWordPolygonMonotoneTwo :
    UnboundOrientedWordPolygonMonotoneTwoStatement.{u, w} := by
  intro G _ Lambda D δ lambda c mu hδ hδ0 hlambda hc hmu
  obtain ⟨kappa, hkappa, hmorse, -⟩ :=
    exists_word_replacement_morse_monotone D lambda c hlambda hδ hδ0
  obtain ⟨eps0, heps0⟩ := exists_nat_gt (12 * ((δ + 6) + 1) + 2 * kappa)
  refine ⟨kappa, hkappa, eps0, ?_⟩
  intro epsC hepsC epsL hle
  have hcloseC : 12 * ((δ + 6) + 1) + 2 * kappa < (epsC : ℝ) :=
    lt_of_lt_of_le heps0 (by exact_mod_cast hepsC)
  have hepsL : 12 * ((δ + 6) + 1) + 2 * kappa < (epsL : ℝ) :=
    lt_of_lt_of_le hcloseC (by exact_mod_cast hle)
  obtain ⟨rho0, hrho0, hscale⟩ := exists_osinUnboundScale_after_epsilon lambda c mu kappa
    (12 * ((δ + 6) + 1)) (100000 * ((δ + 6) + 1)) hlambda hmu epsL hepsL
  refine ⟨rho0, hrho0, ?_⟩
  intro rho hrho n v word A B hclose hends hquasi hshort hdense
  have scale := hscale rho hrho
  obtain ⟨sides, hpoly⟩ := exists_geodesic_replacement_polygon D v n hclose
  have hfirst := replacement_first_class_dense D v word hends A hlambda hc
    (fun i hi hiA => hquasi i hi (Or.inl hiA)) hdense
  have hsmall := replacement_short_class_le D v word hends B hshort
  have hreal : IsHyperbolicSpace (δ + 6) (PointQuot D.alphabet) :=
    isHyperbolicSpace_pointQuot (isHyperbolicSpace_point D.alphabet hδ)
  have hpair := scale.exists_orientedPolygonPair hreal (by linarith)
    (isGeodesicRealisationQuot D.alphabet) hpoly A B hfirst hsmall
  exact scale.orientedWordSidePairTwo_of_orientedClassPair hcloseC hle hreal (by linarith) hmorse
    hpoly hends A B hquasi hpair

end GroupApproximation.GGT.VanKampen.UnboundEstimate

namespace GroupApproximation.GGT.VanKampen

universe u w

open GroupApproximation.WordMetric
open GroupApproximation.GGT.VanKampen.UnboundEstimate

/-- **Dense polygons carry a backwards pair at two thresholds**: connectors below `epsC`, segments
above `epsL`, and short sides at most `epsL`. -/
def OsinLemma94DensePolygonsAntiparallelTwo {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (lambda c : ℝ) (epsC epsL rho K : ℕ) : Prop :=
  ∀ (n d : ℕ), 0 < n →
    ∀ (sideCount : Fin d → ℕ) (v : Fin d → ℕ → G)
      (word : Fin d → ℕ → List (RelLetter G Lambda)) (A B : Fin d → Set ℕ),
      (∑ k : Fin d, sideCount k) ≤ K * n →
      (∀ k, v k (sideCount k) = v k 0) →
      (∀ k i, i < sideCount k → v k (i + 1) = v k i * RelLetter.listVal (word k i)) →
      (∀ k i, i < sideCount k → i ∈ A k ∨ i ∈ B k →
        IsLambdaCQuasiGeodesicWord D lambda c (word k i)) →
      (∀ k i, i < sideCount k → i ∉ B k →
        HullSC.RelWord.IsAdmissible D (word k i) ∧ (word k i).length ≤ epsL) →
      (n : ℝ) * Real.sqrt (rho : ℝ) ≤
        ∑ k : Fin d, classWordLength (word k) (sideCount k) (A k) →
      ∃ k : Fin d, ∃ C : WordConnectorPair D (v k) (word k) (sideCount k) (A k) (B k) epsC,
        C.b' < C.b ∧
          epsL < wordDist D.alphabet.carrier
            (OsinComponents.vertex (v k C.source) (word k C.source) C.a)
            (OsinComponents.vertex (v k C.source) (word k C.source) C.a') ∧
          epsL < wordDist D.alphabet.carrier
            (OsinComponents.vertex (v k C.target) (word k C.target) C.b)
            (OsinComponents.vertex (v k C.target) (word k C.target) C.b')

/-- **The metric half of Lemma 9.4, oriented, at two thresholds.** -/
def OsinLemma94AntiparallelMetricTwoStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w} (D : RelGenSet G Lambda),
    (∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
    ∀ lambda c : ℝ, 0 < lambda → 0 ≤ c →
      ∃ eps0 : ℕ, ∀ epsC : ℕ, eps0 ≤ epsC → ∀ epsL : ℕ, epsC ≤ epsL → ∀ K : ℕ,
        ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
          OsinLemma94DensePolygonsAntiparallelTwo D lambda c epsC epsL rho K

theorem osinLemma94AntiparallelMetricTwo : OsinLemma94AntiparallelMetricTwoStatement.{u, w} := by
  intro G _ Lambda D hhyper lambda c hlambda hc
  obtain ⟨delta, hdelta⟩ := hhyper
  obtain ⟨_, _, eps0, hpolygon⟩ :=
    unboundOrientedWordPolygonMonotoneTwo G Lambda D (delta : ℝ) lambda c 1
      (isHyperbolicSpace_cayley_of_fourPoint D.alphabet hdelta) (by positivity)
      hlambda hc one_pos
  refine ⟨eps0, fun epsC hepsC epsL hle K => ?_⟩
  obtain ⟨rho1, hrho1, hpolygonEps⟩ := hpolygon epsC hepsC epsL hle
  refine ⟨(K + 1) ^ 2 * rho1, mul_pos (by positivity) hrho1, fun rho hrho => ?_⟩
  intro n d hn sideCount v word A B hbudget hclose hends hquasi hshort htotal
  obtain ⟨rho', hrho1', hdiv⟩ : ∃ rho' : ℕ, rho1 ≤ rho' ∧ rho' * (K + 1) ^ 2 ≤ rho :=
    ⟨rho / (K + 1) ^ 2, (Nat.le_div_iff_mul_le (by positivity)).mpr
      (by rw [Nat.mul_comm]; exact hrho), Nat.div_mul_le_self rho ((K + 1) ^ 2)⟩
  have hdivReal : (rho' : ℝ) * ((K : ℝ) + 1) ^ 2 ≤ (rho : ℝ) := by
    exact_mod_cast hdiv
  have hK : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  have hsqrt : Real.sqrt (rho' : ℝ) * ((K : ℝ) + 1) ≤ Real.sqrt (rho : ℝ) := by
    have h := Real.sqrt_le_sqrt hdivReal
    rwa [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hK] at h
  have hpos : 0 < Real.sqrt (rho' : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le hrho1 hrho1')
  have hKs : 0 ≤ (K : ℝ) * Real.sqrt (rho' : ℝ) := by positivity
  have hst : (K : ℝ) * (Real.sqrt (rho' : ℝ) / 240) < Real.sqrt (rho : ℝ) := by
    linarith
  obtain ⟨k, hk⟩ := exists_component_dense_of_sideBudget n K hn
    (by positivity : (0 : ℝ) ≤ Real.sqrt (rho' : ℝ) / 240) hst sideCount
    (fun k => classWordLength (word k) (sideCount k) (A k)) hbudget htotal
  have pair := hpolygonEps rho' hrho1' (sideCount k) (v k) (word k) (A k) (B k) (hclose k)
    (hends k) (hquasi k) (hshort k) (by simpa only [mul_div_assoc] using hk)
  obtain ⟨C, hlongS, hlongT⟩ :=
    pair.exists_connectors hle (fun i hi hiAB => (hquasi k i hi hiAB).1)
  exact ⟨k, C.toWordConnectorPair, C.target_backward, hlongS, hlongT⟩

end GroupApproximation.GGT.VanKampen

open GroupApproximation.GGT.VanKampen

#audit_axioms UnboundEstimate.OrientedWordSidePairTwo.exists_connectors
#audit_axioms UnboundEstimate.OsinUnboundScale.orientedWordSidePairTwo_of_parameters
#audit_closed_axioms UnboundEstimate.unboundOrientedWordPolygonMonotoneTwo
#audit_closed_axioms osinLemma94AntiparallelMetricTwo
