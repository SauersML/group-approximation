import GroupApproximation.GGT.CayleyGeodesicMorse
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.DGOPolygonGeodesicChain

/-!
# Geodesic replacements of Osin quasi-geodesic words

The original `lambda,c` inequality becomes a discrete chain inequality with
reciprocal multiplicative parameter and the ceiling of the additive error.
The Cayley realization Morse theorem then supplies one radius for every word,
basepoint, and geodesic replacement. No proximity witness is assumed.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open CayleyGeodesicModel OsinComponents

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}
  {D : RelGenSet G Lambda} {lambda c : ℝ}

/-- The chain has the original Osin multiplicative parameter, reciprocated
to match the discrete Morse API. Only the additive error is rounded up. -/
theorem IsLambdaCQuasiGeodesicWord.to_chainAt
    {word : List (RelLetter G Lambda)} (h : IsLambdaCQuasiGeodesicWord D lambda c word)
    (v : G) :
    IsQuasiGeodesicChainAt D.alphabet.carrier lambda⁻¹ ⌈c⌉₊
      (OsinComponents.vertex v word) word.length := by
  intro i j hij hj
  refine ⟨?_, wordDist_vertex_le' D h.1 v hij hj⟩
  rw [vertex_eq_mul_vertex_one word v i, vertex_eq_mul_vertex_one word v j,
    wordDist_left_invariant, div_inv_eq_mul]
  have hquasi := h.2 i j hij hj
  have hceil : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
  nlinarith

/-- The distance between the endpoints of a word is its represented norm,
also in the geodesic realization. -/
theorem word_replacement_distance (v : G) (word : List (RelLetter G Lambda)) :
    dist (vertexQuot D.alphabet v) (vertexQuot D.alphabet (v * RelLetter.listVal word)) =
      (wordNorm D.alphabet.carrier (RelLetter.listVal word) : ℝ) := by
  rw [dist_vertexQuot]
  simp only [wordDist, inv_mul_cancel_left]

/-- One Morse radius supplies actual original-word indices near every point
of every geodesic replacement, and supplies the reverse proximity as well. -/
theorem exists_word_replacement_morse (D : RelGenSet G Lambda)
    (lambda c : ℝ) (hlambda : 0 < lambda) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley D.alphabet)) (hδ0 : 0 ≤ δ) :
    ∃ kappa : ℝ, 0 ≤ kappa ∧
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
              dist (f t) (vertexQuot D.alphabet (OsinComponents.vertex v word i)) ≤ kappa) := by
  obtain ⟨kappa, hkappa, hnear⟩ := exists_chain_realization_hausdorff_bound D.alphabet
    lambda⁻¹ ⌈c⌉₊ (inv_pos.mpr hlambda) hδ hδ0
  refine ⟨kappa, hkappa, ?_⟩
  intro word hword v f hf hf0 hf1
  have hzero : OsinComponents.vertex v word 0 = v := vertex_zero v word
  have hend : OsinComponents.vertex v word word.length = v * RelLetter.listVal word := by
    rw [vertex_eq_mul_listVal_take, List.take_length]
  have hf' : IsGeodesicSegment f 0
      (dist (vertexQuot D.alphabet (OsinComponents.vertex v word 0))
        (vertexQuot D.alphabet (OsinComponents.vertex v word word.length))) := by
    simpa only [hzero, hend] using hf
  have hf0' : f 0 = vertexQuot D.alphabet (OsinComponents.vertex v word 0) := by
    simpa only [hzero] using hf0
  have hf1' : f (dist (vertexQuot D.alphabet (OsinComponents.vertex v word 0))
        (vertexQuot D.alphabet (OsinComponents.vertex v word word.length))) =
      vertexQuot D.alphabet (OsinComponents.vertex v word word.length) := by
    simpa only [hzero, hend] using hf1
  simpa only [hzero, hend] using
    hnear (OsinComponents.vertex v word) word.length (hword.to_chainAt v) f hf' hf0' hf1'

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.to_chainAt
#audit_axioms GroupApproximation.GGT.VanKampen.word_replacement_distance
#audit_axioms GroupApproximation.GGT.VanKampen.exists_word_replacement_morse
