import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.OsinTheorem54SepSubGeodesic
import GroupApproximation.GGT.OsinGeodesicWord

/-!
# Geodesic words are quasi-geodesic

Osin's relative Greendlinger lemma is stated for diagrams whose outer boundary
is a `(λ, c)`-quasi-geodesic word in `Γ(G, X ⊔ H)`.  Hull's Lemma 4.4 applies
it to a short word of the kernel, and the word can be taken geodesic: a
geodesic word from the identity is `(λ, c)`-quasi-geodesic for every
`λ ≤ 1` and `c ≥ 0`, because each of its segments is again geodesic
(`OsinComponents.isGeodesicWord_segment`), so the relative distance between two
of its vertices is the number of letters between them.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.WordMetric

universe u w

/-- A geodesic word from the identity is `(λ, c)`-quasi-geodesic for every
`λ ≤ 1` and `c ≥ 0`. -/
theorem isLambdaCQuasiGeodesicWord_of_isGeodesicWord
    {G : Type u} [Group G] {Lambda : Type w} (D : GGT.RelGenSet G Lambda)
    {g : G} {w : List (GGT.RelLetter G Lambda)}
    (hw : GGT.OsinComponents.IsGeodesicWord D 1 g w)
    {lambda c : ℝ} (hlambda : lambda ≤ 1) (hc : 0 ≤ c) :
    IsLambdaCQuasiGeodesicWord D lambda c w := by
  refine ⟨hw.1, ?_⟩
  intro i j hij hj
  have hseg := GGT.OsinComponents.isGeodesicWord_segment D hw hij hj
  have hlen : ((w.drop i).take (j - i)).length = j - i := by
    rw [List.length_take, List.length_drop]
    omega
  have hdist : wordDist D.alphabet.carrier
      (GGT.OsinComponents.vertex 1 w i) (GGT.OsinComponents.vertex 1 w j) =
        j - i := by
    rw [← hseg.2.2]
    exact hlen
  rw [hdist]
  have hnonneg : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hscale : lambda * ((j - i : ℕ) : ℝ) ≤ 1 * ((j - i : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hlambda hnonneg
  rw [one_mul] at hscale
  linarith

/-- Every element is spelled by a geodesic word from the identity, and that
word is `(λ, c)`-quasi-geodesic for every `λ ≤ 1` and `c ≥ 0`. -/
theorem exists_geodesicWord_isLambdaCQuasiGeodesicWord
    {G : Type u} [Group G] {Lambda : Type w} (D : GGT.RelGenSet G Lambda)
    (g : G) {lambda c : ℝ} (hlambda : lambda ≤ 1) (hc : 0 ≤ c) :
    ∃ w : List (GGT.RelLetter G Lambda),
      GGT.OsinComponents.IsGeodesicWord D 1 g w ∧
        IsLambdaCQuasiGeodesicWord D lambda c w := by
  obtain ⟨w, hw⟩ := GGT.OsinComponents.existsGeodesicWord D 1 g
  exact ⟨w, hw, isLambdaCQuasiGeodesicWord_of_isGeodesicWord D hw hlambda hc⟩

end VanKampen
end GGT
end GroupApproximation
