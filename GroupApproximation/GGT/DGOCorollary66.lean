import GroupApproximation.GGT.ElementaryFiniteTransversalConsequences

/-!
# DGO Corollary 6.6: one power normalized by the elementary closure

For each element of `E(h)`, the stable-translation argument in
`ElementaryClosure` already gives a possibly element-dependent nonzero power
of `h` that is conjugated to itself or its inverse.  DGO Lemma 6.5 says only
finitely many `⟨h⟩`-cosets cover `E(h)`.  Multiplying the finitely many
representative exponents produces one nonzero power normalized by all of
`E(h)`, which is the uniform conclusion used in Corollary 6.6.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- A representative has a nonzero normalised power if it lies in `E(h)`;
outside `E(h)` the implication is vacuous.  This total form permits finite
choice over a transversal that may contain unused representatives. -/
theorem exists_conj_zpow_eq_or_of_mem_imp
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x) (a : G) :
    ∃ n : ℤ, n ≠ 0 ∧ (a ∈ elementaryClosure h →
      (a * h ^ n * a⁻¹ = h ^ n ∨ a * h ^ n * a⁻¹ = h ^ (-n))) := by
  by_cases ha : a ∈ elementaryClosure h
  · obtain ⟨n, hn, hrel⟩ :=
      conj_zpow_eq_or_of_mem_elementaryClosure hiso hlox ha
    exact ⟨n, hn, fun _ => hrel⟩
  · exact ⟨1, one_ne_zero, fun hmem => (ha hmem).elim⟩

/-- **DGO Corollary 6.6, uniform-power clause.**  If `⟨h⟩` has finite index in
`E(h)`, one nonzero power of `h` is conjugated to itself or its inverse by
every element of `E(h)`. -/
theorem exists_uniform_normal_zpow_of_finiteTransversal
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x)
    (hfin : ElementaryClosureFiniteTransversal h) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ g : G, g ∈ elementaryClosure h →
      (g * h ^ N * g⁻¹ = h ^ N ∨ g * h ^ N * g⁻¹ = h ^ (-N)) := by
  classical
  obtain ⟨F, hF, hcover⟩ := hfin
  choose n hn hrel using fun a : G =>
    exists_conj_zpow_eq_or_of_mem_imp hiso hlox a
  let N : ℤ := ∏ a ∈ hF.toFinset, n a
  have hN : N ≠ 0 := by
    dsimp [N]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hn a
  refine ⟨N, hN, ?_⟩
  intro g hg
  obtain ⟨c, a, haF, rfl⟩ := hcover g hg
  have haE : a ∈ elementaryClosure h := by
    have hhpow : h ^ c ∈ elementaryClosure h :=
      Subgroup.zpow_mem _ (self_mem_elementaryClosure h) c
    exact ((elementaryClosure h).mul_mem_cancel_left hhpow).mp
      (show h ^ c * a ∈ elementaryClosure h from hg)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (hF.mem_toFinset.mpr haF)
  have hNk : N = n a * k := by simpa [N] using hk
  have hconjN :
      a * h ^ N * a⁻¹ = h ^ N ∨ a * h ^ N * a⁻¹ = h ^ (-N) := by
    rcases hrel a haE with hpos | hneg
    · left
      calc
        a * h ^ N * a⁻¹ = a * (h ^ n a) ^ k * a⁻¹ := by rw [hNk, zpow_mul]
        _ = (a * h ^ n a * a⁻¹) ^ k := by rw [conj_zpow_eq]
        _ = (h ^ n a) ^ k := by rw [hpos]
        _ = h ^ N := by rw [← zpow_mul, ← hNk]
    · right
      calc
        a * h ^ N * a⁻¹ = a * (h ^ n a) ^ k * a⁻¹ := by rw [hNk, zpow_mul]
        _ = (a * h ^ n a * a⁻¹) ^ k := by rw [conj_zpow_eq]
        _ = (h ^ (-n a)) ^ k := by rw [hneg]
        _ = h ^ (-N) := by
          rw [← zpow_mul]
          congr 1
          rw [hNk]
          ring
  rcases hconjN with hpos | hneg
  · left
    calc
      (h ^ c * a) * h ^ N * (h ^ c * a)⁻¹ =
          h ^ c * (a * h ^ N * a⁻¹) * h ^ (-c) := by group
      _ = h ^ c * h ^ N * h ^ (-c) := by rw [hpos]
      _ = h ^ N := by rw [← zpow_add, ← zpow_add]; congr 1; ring
  · right
    calc
      (h ^ c * a) * h ^ N * (h ^ c * a)⁻¹ =
          h ^ c * (a * h ^ N * a⁻¹) * h ^ (-c) := by group
      _ = h ^ c * h ^ (-N) * h ^ (-c) := by rw [hneg]
      _ = h ^ (-N) := by rw [← zpow_add, ← zpow_add]; congr 1; ring

end Elementary
end GGT
end GroupApproximation
