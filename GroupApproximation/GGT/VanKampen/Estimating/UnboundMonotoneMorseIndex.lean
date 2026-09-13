import GroupApproximation.GGT.VanKampen.WordGeodesicReplacement
import GroupApproximation.GGT.VanKampen.Estimating.UnboundPolygonGeometry
import GroupApproximation.GGT.OsinPenetration
import GroupApproximation.Meta.AxiomGuard

/-!
# Monotone Morse indices along a geodesic replacement

Osin, *Small cancellations over relatively hyperbolic groups and embedding
theorems*, arXiv:math/0411039v3, Appendix, proof of Lemma 9.4.  The metric part
replaces each quasi-geodesic side of a cyclic word polygon by a geodesic, finds
two long fellow-travelling segments on two replacement sides, and moves their
four endpoints to original vertices by Morse proximity
(`OsinUnboundScale.exists_originalArcPair_of_class_near`).  The planar Case 1
contradiction needs the moved endpoints to keep the orientation of the
parameters, `a < a'` on the source side and `b' < b` on the target side.  Morse
proximity chooses the four vertex indices existentially, and that loses it.

**Monotone index choice** (`index_lt_of_prefix_near`).  Let `side` be a geodesic
starting at the vertex `v` of a `(λ, c)`-quasi-geodesic word, and let `side u`
and `side u'` lie within `κ` of the vertices `a` and `a'` of the word, where `κ`
is a Morse radius for all such words.  If `u + (3κ + 6δ) < u'`, then `a < a'`.
Suppose instead `a' ≤ a`.  The prefix `word.take a` is again quasi-geodesic, so
its vertex `a'` lies within `κ` of a point `g s₀` of a geodesic `g` from `v` to
the vertex `a`.  The geodesic `g` and the initial piece `side|[0,u]` have
endpoints within `κ` of each other, so `g s₀` lies within `κ + 6δ` of some
`side s` with `s ≤ u` (`exists_close_of_endpoints_close`).  Then
`u' - s = dist (side u') (side s) ≤ 3κ + 6δ`, while `u' - s ≥ u' - u`.

`exists_word_replacement_morse_monotone` packages one radius for Morse proximity
and for the monotone choice in the geodesic realisation of the Cayley graph, whose
hyperbolicity constant is `δ + 6`.  `OsinUnboundScale.morse_gap_lt` shows that the
segment length of Osin's numerical scale exceeds the margin, so an oriented pair
of long segments passes its orientation to the original indices.
-/

namespace GroupApproximation.GGT.VanKampen.UnboundEstimate

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- A prefix of a word visits the same first vertices as the word. -/
theorem vertex_take_prefix (v : G) :
    ∀ (word : List (RelLetter G Lambda)) (m k : ℕ), k ≤ m →
      OsinComponents.vertex v (word.take m) k = OsinComponents.vertex v word k
  | _, _, 0, _ => by simp only [OsinComponents.vertex_zero]
  | [], _, _ + 1, _ => by rw [List.take_nil]
  | _ :: _, 0, _ + 1, h => absurd h (by omega)
  | b :: t, m + 1, k + 1, h => by
      rw [List.take_succ_cons, OsinComponents.vertex_cons_succ,
        OsinComponents.vertex_cons_succ, vertex_take_prefix (v * b.val) t m k (by omega)]

/-- A prefix of a `(λ, c)`-quasi-geodesic word is `(λ, c)`-quasi-geodesic. -/
theorem isLambdaCQuasiGeodesicWord_take_prefix {D : RelGenSet G Lambda} {lambda c : ℝ}
    {word : List (RelLetter G Lambda)} (h : IsLambdaCQuasiGeodesicWord D lambda c word)
    (m : ℕ) : IsLambdaCQuasiGeodesicWord D lambda c (word.take m) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact h.1 x (List.mem_of_mem_take hx)
  · intro i j hij hj
    have hjm : j ≤ m := le_trans hj (List.length_take_le m word)
    have hjw : j ≤ word.length := le_trans hj (List.length_take_le' m word)
    rw [vertex_take_prefix 1 word m i (le_trans hij hjm), vertex_take_prefix 1 word m j hjm]
    exact h.2 i j hij hjw

/-- The conclusion of `exists_word_replacement_morse` at one radius `kappa`: Morse
proximity in both directions between every `(λ, c)`-quasi-geodesic word and every
geodesic replacement of it in the Cayley realisation. -/
def IsWordMorseRadius (D : RelGenSet G Lambda) (lambda c kappa : ℝ) : Prop :=
  ∀ (word : List (RelLetter G Lambda)), IsLambdaCQuasiGeodesicWord D lambda c word →
    ∀ (v : G) (f : ℝ → PointQuot D.alphabet),
      IsGeodesicSegment f 0
        (dist (vertexQuot D.alphabet v)
          (vertexQuot D.alphabet (v * RelLetter.listVal word))) →
      f 0 = vertexQuot D.alphabet v →
      f (dist (vertexQuot D.alphabet v)
        (vertexQuot D.alphabet (v * RelLetter.listVal word))) =
          vertexQuot D.alphabet (v * RelLetter.listVal word) →
      (∀ i ≤ word.length, ∃ t ∈ Set.Icc (0 : ℝ)
          (dist (vertexQuot D.alphabet v)
            (vertexQuot D.alphabet (v * RelLetter.listVal word))),
        dist (vertexQuot D.alphabet (OsinComponents.vertex v word i)) (f t) ≤ kappa) ∧
      (∀ t ∈ Set.Icc (0 : ℝ)
          (dist (vertexQuot D.alphabet v)
            (vertexQuot D.alphabet (v * RelLetter.listVal word))),
        ∃ i ≤ word.length,
          dist (f t) (vertexQuot D.alphabet (OsinComponents.vertex v word i)) ≤ kappa)

/-- **Monotone Morse indices.**  Let `side` be a geodesic from the vertex `v` of a
`(λ, c)`-quasi-geodesic word, in a `δ`-hyperbolic realisation, and let `kappa` be a
Morse radius.  If `side u` is `kappa`-close to the vertex `a`, `side u'` is
`kappa`-close to the vertex `a'`, and `u + (3 kappa + 6 δ) < u'`, then `a < a'`. -/
theorem index_lt_of_prefix_near {D : RelGenSet G Lambda} {lambda c kappa δ : ℝ}
    (hδ : IsHyperbolicSpace δ (PointQuot D.alphabet)) (hδ0 : 0 ≤ δ)
    (hmorse : IsWordMorseRadius D lambda c kappa)
    {word : List (RelLetter G Lambda)} (hword : IsLambdaCQuasiGeodesicWord D lambda c word)
    {v : G} {L : ℝ} {side : ℝ → PointQuot D.alphabet}
    (hside : IsGeodesicSegment side 0 L) (hside0 : side 0 = vertexQuot D.alphabet v)
    {u u' : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) L) (hu' : u' ∈ Set.Icc (0 : ℝ) L)
    {a a' : ℕ} (ha : a ≤ word.length)
    (hnear : dist (side u) (vertexQuot D.alphabet (OsinComponents.vertex v word a)) ≤ kappa)
    (hnear' :
      dist (side u') (vertexQuot D.alphabet (OsinComponents.vertex v word a')) ≤ kappa)
    (hgap : u + (3 * kappa + 6 * δ) < u') :
    a < a' := by
  by_contra hcon
  have ha'a : a' ≤ a := by omega
  have hkappa : 0 ≤ kappa := le_trans dist_nonneg hnear
  -- the prefix read up to the vertex `a` is quasi-geodesic and ends there
  have hpre : IsLambdaCQuasiGeodesicWord D lambda c (word.take a) :=
    isLambdaCQuasiGeodesicWord_take_prefix hword a
  have hplen : (word.take a).length = a := by
    rw [List.length_take]
    exact min_eq_left ha
  have hpend : v * RelLetter.listVal (word.take a) = OsinComponents.vertex v word a := by
    rw [← OsinComponents.vertex_length, hplen, vertex_take_prefix v word a a le_rfl]
  -- a geodesic `g` from `v` to the vertex `a`; the vertex `a'` is near a point of it
  obtain ⟨g, hg, hg0, hg1⟩ := isGeodesicRealisationQuot D.alphabet
    (vertexQuot D.alphabet v) (vertexQuot D.alphabet (v * RelLetter.listVal (word.take a)))
  obtain ⟨s₀, hs₀, hs₀d⟩ :=
    (hmorse (word.take a) hpre v g hg hg0 hg1).1 a' (by rw [hplen]; exact ha'a)
  rw [vertex_take_prefix v word a a' ha'a] at hs₀d
  -- the initial piece `side|[0,u]` has endpoints near those of `g`
  have hdist : dist (side 0) (side u) = u := by
    rw [hside 0 ⟨le_rfl, le_trans hu.1 hu.2⟩ u hu, zero_sub, abs_neg, abs_of_nonneg hu.1]
  have hsub : IsGeodesicSegment side 0 (dist (side 0) (side u)) := by
    rw [hdist]
    intro s hs t ht
    exact hside s ⟨hs.1, le_trans hs.2 hu.2⟩ t ⟨ht.1, le_trans ht.2 hu.2⟩
  have hx : dist (vertexQuot D.alphabet v) (side 0) ≤ kappa := by
    rw [hside0, dist_self]
    exact hkappa
  have hy : dist (vertexQuot D.alphabet (v * RelLetter.listVal (word.take a))) (side u) ≤
      kappa := by
    rw [hpend, dist_comm]
    exact hnear
  obtain ⟨s, hs, hsd⟩ := Olshanskii.exists_close_of_endpoints_close hδ hδ0
    (isGeodesicRealisationQuot D.alphabet) hg hg0 hg1 hsub rfl (by rw [hdist]) hx hy hs₀
  rw [hdist] at hs
  have hsL : s ∈ Set.Icc (0 : ℝ) L := ⟨hs.1, le_trans hs.2 hu.2⟩
  have hsu' : 0 ≤ u' - s := by linarith [hs.2]
  have hfar : dist (side u') (side s) = u' - s := by
    rw [hside u' hu' s hsL, abs_of_nonneg hsu']
  have htri := dist_triangle4 (side u')
    (vertexQuot D.alphabet (OsinComponents.vertex v word a')) (g s₀) (side s)
  linarith [hs.2]

/-- **One Morse radius with monotone indices.**  In the geodesic realisation of a
`δ`-hyperbolic Cayley graph, one radius `kappa` gives Morse proximity for every
`(λ, c)`-quasi-geodesic word, and the vertex indices close to two points of a
geodesic from the start of the word increase with the parameter once the points
are more than `3 kappa + 6 (δ + 6)` apart. -/
theorem exists_word_replacement_morse_monotone (D : RelGenSet G Lambda)
    (lambda c : ℝ) (hlambda : 0 < lambda) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley D.alphabet)) (hδ0 : 0 ≤ δ) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧ IsWordMorseRadius D lambda c kappa ∧
      ∀ (word : List (RelLetter G Lambda)), IsLambdaCQuasiGeodesicWord D lambda c word →
        ∀ (v : G) (L : ℝ) (side : ℝ → PointQuot D.alphabet),
          IsGeodesicSegment side 0 L → side 0 = vertexQuot D.alphabet v →
          ∀ u ∈ Set.Icc (0 : ℝ) L, ∀ u' ∈ Set.Icc (0 : ℝ) L,
            ∀ a ≤ word.length, ∀ a' : ℕ,
              dist (side u) (vertexQuot D.alphabet (OsinComponents.vertex v word a)) ≤
                kappa →
              dist (side u') (vertexQuot D.alphabet (OsinComponents.vertex v word a')) ≤
                kappa →
              u + (3 * kappa + 6 * (δ + 6)) < u' → a < a' := by
  obtain ⟨kappa, hkappa, hmorse⟩ := exists_word_replacement_morse D lambda c hlambda hδ hδ0
  refine ⟨kappa, hkappa, hmorse, ?_⟩
  intro word hword v L side hside hside0 u hu u' hu' a ha a' hnear hnear' hgap
  exact index_lt_of_prefix_near
    (isHyperbolicSpace_pointQuot (isHyperbolicSpace_point D.alphabet hδ)) (by linarith)
    hmorse hword hside hside0 hu hu' ha hnear hnear' hgap

/-- **The scale leaves room for the monotone margin.**  The segment length
`(λ √ρ / 240 - c) / 1000` of Osin's numerical scale exceeds `3 kappa + 6 δ`,
because equation (36) and the shortening margin give it more than
`12 (δ + 1) + 4 kappa`. -/
theorem OsinUnboundScale.morse_gap_lt {δ lambda c mu kappa : ℝ} {eps rho : ℕ}
    (scale : OsinUnboundScale lambda c mu kappa (12 * (δ + 1)) (100000 * (δ + 1)) eps rho)
    (hkappa : 0 ≤ kappa) (hδ0 : 0 ≤ δ) :
    3 * kappa + 6 * δ < (lambda * Real.sqrt (rho : ℝ) / 240 - c) / 1000 := by
  have hclose := scale.epsilon_large
  have hlong := scale.shortcut_shortens
  linarith

end GroupApproximation.GGT.VanKampen.UnboundEstimate

#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.vertex_take_prefix
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.isLambdaCQuasiGeodesicWord_take_prefix
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.index_lt_of_prefix_near
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.exists_word_replacement_morse_monotone
#audit_axioms GroupApproximation.GGT.VanKampen.UnboundEstimate.OsinUnboundScale.morse_gap_lt
