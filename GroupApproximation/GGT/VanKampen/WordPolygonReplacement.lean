import GroupApproximation.GGT.VanKampen.WordGeodesicReplacement
import GroupApproximation.GGT.OlshanskiiPolygonClasses

/-!
# Replacement polygons and their class lengths

A cyclic sequence of based words supplies the actual polygon vertices. Each
side is replaced by a geodesic in the Cayley metric realization. The first
class retains its quasi-geodesic lower bound, and the short class retains its
word-length upper bound. These are the two length estimates used in Osin's
unbound-arc argument.
-/

namespace GroupApproximation.GGT.VanKampen

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Olshanskii
open CayleyGeodesicModel OsinComponents Finset

universe u w
variable {G : Type u} [Group G] {Lambda : Type w}

/-- Sum of original word lengths in one class. -/
noncomputable def classWordLength (word : ℕ → List (RelLetter G Lambda))
    (n : ℕ) (A : Set ℕ) : ℝ := by
  classical
  exact ∑ i ∈ range n, if i ∈ A then (word i).length else 0

/-- Any closed vertex cycle in the realization has simultaneous geodesic
replacements of all its sides. -/
theorem exists_geodesic_replacement_polygon (D : RelGenSet G Lambda)
    (v : ℕ → G) (n : ℕ) (hclose : v n = v 0) :
    ∃ sides : ℕ → ℝ → PointQuot D.alphabet,
      IsClosedPolygonAt (fun i => vertexQuot D.alphabet (v i)) sides 0 n := by
  classical
  choose sides hgeo hzero hend using
    (fun i : ℕ => isGeodesicRealisationQuot D.alphabet
      (vertexQuot D.alphabet (v i)) (vertexQuot D.alphabet (v (i + 1))))
  refine ⟨sides, ⟨fun i _ _ => ⟨hgeo i, hzero i, hend i⟩, ?_⟩⟩
  simp only [zero_add, hclose]

/-- The original word's quasi-geodesic inequality controls the exact length
of its geodesic replacement. -/
theorem word_replacement_lower (D : RelGenSet G Lambda) {lambda c : ℝ}
    {word : List (RelLetter G Lambda)}
    (hword : IsLambdaCQuasiGeodesicWord D lambda c word) (v : G) :
    lambda * (word.length : ℝ) - c ≤
      dist (vertexQuot D.alphabet v) (vertexQuot D.alphabet (v * RelLetter.listVal word)) := by
  rw [word_replacement_distance]
  have h := hword.2 0 word.length (Nat.zero_le _) (le_refl _)
  simpa only [Nat.sub_zero, vertex_zero, vertex_eq_mul_listVal_take,
    List.take_length, List.take_zero, RelLetter.listVal_nil, one_mul, wordDist_one_left] using h

/-- A first class with large original total length has the required large
total after geodesic replacement, paying the additive error per side. -/
theorem replacement_first_class_dense (D : RelGenSet G Lambda)
    (v : ℕ → G) (word : ℕ → List (RelLetter G Lambda)) {n : ℕ}
    (hends : ∀ i < n, v (i + 1) = v i * RelLetter.listVal (word i))
    (A : Set ℕ) {lambda c t : ℝ} (hlambda : 0 < lambda) (hc : 0 ≤ c)
    (hquasi : ∀ i < n, i ∈ A → IsLambdaCQuasiGeodesicWord D lambda c (word i))
    (hdense : (n : ℝ) * t / 240 < classWordLength word n A) :
    (lambda * t / 240 - c) * n <
      classLength (fun i => vertexQuot D.alphabet (v i)) n A := by
  classical
  have hper : ∀ i ∈ range n,
      lambda * (if i ∈ A then ((word i).length : ℝ) else 0) - c ≤
        if i ∈ A then dist (vertexQuot D.alphabet (v i))
          (vertexQuot D.alphabet (v (i + 1))) else 0 := by
    intro i hi
    by_cases hiA : i ∈ A
    · rw [if_pos hiA, if_pos hiA, hends i (mem_range.mp hi)]
      exact word_replacement_lower D (hquasi i (mem_range.mp hi) hiA) (v i)
    · rw [if_neg hiA, if_neg hiA, mul_zero]
      linarith
  have hsum := sum_le_sum hper
  have hsum' : lambda * classWordLength word n A - (n : ℝ) * c ≤
      classLength (fun i => vertexQuot D.alphabet (v i)) n A := by
    simpa only [classWordLength, classLength, sum_sub_distrib, ← mul_sum,
      sum_const, card_range, nsmul_eq_mul] using hsum
  have hscale := mul_lt_mul_of_pos_left hdense hlambda
  nlinarith

/-- Admissible short side words bound the total length of the third class
after replacement. They need no quasi-geodesic hypothesis. -/
theorem replacement_short_class_le (D : RelGenSet G Lambda)
    (v : ℕ → G) (word : ℕ → List (RelLetter G Lambda)) {n eps : ℕ}
    (hends : ∀ i < n, v (i + 1) = v i * RelLetter.listVal (word i))
    (B : Set ℕ)
    (hshort : ∀ i < n, i ∉ B →
      HullSC.RelWord.IsAdmissible D (word i) ∧ (word i).length ≤ eps) :
    classLength (fun i => vertexQuot D.alphabet (v i)) n Bᶜ ≤ (eps : ℝ) * n := by
  classical
  calc
    _ ≤ ∑ _i ∈ range n, (eps : ℝ) := by
      apply sum_le_sum
      intro i hi
      by_cases hiB : i ∈ B
      · simp only [Set.mem_compl_iff, hiB, not_true_eq_false, if_false]
        positivity
      · simp only [Set.mem_compl_iff, if_pos hiB]
        rw [hends i (mem_range.mp hi), word_replacement_distance]
        obtain ⟨hletters, hlen⟩ := hshort i (mem_range.mp hi) hiB
        exact_mod_cast (wordNorm_listVal_le D (word i) hletters).trans hlen
    _ = _ := by simp [mul_comm]

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.exists_geodesic_replacement_polygon
#audit_axioms GroupApproximation.GGT.VanKampen.replacement_first_class_dense
#audit_axioms GroupApproximation.GGT.VanKampen.replacement_short_class_le
