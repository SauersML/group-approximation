import GroupApproximation.GGT.VanKampen.RelativeGreendlinger
import GroupApproximation.GGT.DGOQuasiGeodesicChainHausdorff
import GroupApproximation.GGT.OsinTheorem54SepSplit
import GroupApproximation.GGT.OsinTheorem54SepFourGonPinning

/-!
# GL06h2: vertex estimates for a `(λ, c)`-quasi-geodesic relator

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121).

* `chainAt_of_quasiGeodesicWord`: the vertices of a `(λ, c)`-quasi-geodesic word form a
  `(1/λ, ⌈c⌉)` quasi-geodesic chain, the input of the Morse lemma
  `GGT.exists_chainAt_hausdorff_bound`.
* `long_vertexDist_of_quasiGeodesic`: vertices at index distance `K ≥ (L + c)/λ` are at word
  distance at least `L`.
* `local_of_between`: a vertex `R`-close to a between point has excess at most `2R`.
-/

namespace GroupApproximation.Full.GL06h2

universe u w

open GroupApproximation.WordMetric
open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

variable {G : Type u} [Group G] {Lambda : Type w}

theorem vertex_length_eq_listVal (word : List (RelLetter G Lambda)) :
    OsinComponents.vertex 1 word word.length = RelLetter.listVal word := by
  rw [OsinComponents.vertex_eq_mul_listVal_take word 1 word.length, List.take_length, one_mul]

/-- The vertices of a `(λ, c)`-quasi-geodesic word are a `(1/λ, ⌈c⌉)` quasi-geodesic chain. -/
theorem chainAt_of_quasiGeodesicWord (D : RelGenSet G Lambda) {lambda c : ℝ}
    {word : List (RelLetter G Lambda)} (hq : IsLambdaCQuasiGeodesicWord D lambda c word) :
    IsQuasiGeodesicChainAt D.alphabet.carrier (1 / lambda) ⌈c⌉₊
      (OsinComponents.vertex 1 word) word.length := by
  intro i j hij hj
  refine ⟨?_, OsinComponents.wordDist_vertex_le D hq.1 hij hj⟩
  have h1 := hq.2 i j hij hj
  have hc : c ≤ (⌈c⌉₊ : ℝ) := Nat.le_ceil c
  rw [div_div_eq_mul_div, div_one, mul_comm]
  linarith

/-- Vertices of a `(λ, c)`-quasi-geodesic word at index distance at least `K ≥ (L + c)/λ` are at
word distance at least `L`. -/
theorem long_vertexDist_of_quasiGeodesic (D : RelGenSet G Lambda) {lambda c : ℝ}
    (hlam : 0 < lambda) {word : List (RelLetter G Lambda)}
    (hq : IsLambdaCQuasiGeodesicWord D lambda c word) {L K : ℕ}
    (hKc : ((L : ℝ) + c) / lambda ≤ K) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ word.length)
    (hKij : K ≤ j - i) :
    L ≤ wordDist D.alphabet.carrier (OsinComponents.vertex 1 word i)
      (OsinComponents.vertex 1 word j) := by
  have h1 := hq.2 i j hij hj
  have h2 : ((L : ℝ) + c) / lambda ≤ ((j - i : ℕ) : ℝ) :=
    le_trans hKc (Nat.cast_le.mpr hKij)
  rw [div_le_iff₀ hlam, mul_comm] at h2
  have h3 : (L : ℝ) ≤ ((wordDist D.alphabet.carrier (OsinComponents.vertex 1 word i)
      (OsinComponents.vertex 1 word j) : ℕ) : ℝ) := by
    linarith
  exact_mod_cast h3

/-- A point `R`-close to a point between `y₀` and `yₙ` has Gromov excess at most `2R`. -/
theorem local_of_between {S : Set G} (hS : IsSymmetricGeneratingSet S) {R : ℕ}
    {y0 yi yn p : G} (hp : Hyperbolic.IsBetween S y0 p yn) (hR : wordDist S yi p ≤ R) :
    wordDist S y0 yi + wordDist S yi yn ≤ wordDist S y0 yn + 2 * R := by
  have h1 := wordDist_triangle hS y0 p yi
  have h2 := wordDist_triangle hS yi p yn
  have h3 := wordDist_comm hS p yi
  have h4 : wordDist S y0 p + wordDist S p yn = wordDist S y0 yn := hp
  omega

end GroupApproximation.Full.GL06h2
