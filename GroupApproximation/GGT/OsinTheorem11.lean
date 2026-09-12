import GroupApproximation.GGT.OsinUniformlyProper
import GroupApproximation.GGT.OsinFarQuasiStabilizer
import GroupApproximation.GGT.ElementaryBowditchProof
import GroupApproximation.GGT.ElementaryOsinSNormal

/-!
# Unbounded orbits give loxodromic elements (Osin 2016, Theorem 1.1)

Osin, *Acylindrically hyperbolic groups* (arXiv:1304.1246), Theorem 1.1, first
half of its proof:

> Let us first prove that if `G` has unbounded orbits, then `G` contains
> loxodromic elements.

This module proves it for every subgroup, at a geodesic hyperbolic space with an
acylindrical isometric action (`hasLoxodromicOfUnbounded_of_geodesic`).  That is
the repository's named Prop `Elementary.HasLoxodromicOfUnbounded`.  It is then
transported to Hull's Cayley graph through its geodesic realisation
(`hasLoxodromicOfUnbounded_cayley`).

The proof is Osin's and splits on uniform properness.

* **Uniformly proper**: Lemma 3.4 (`exists_loxodromic_of_uniformlyProper`).
* **Otherwise**: some quasi-stabilizer `A(s₀) = {a ∈ K | d(s₀, a s₀) ≤ C}` has
  `2N + 1` elements, where `N` is the constant of Lemma 3.6 for
  `ε = 2C + 2δ + 1`.  Take `t ∈ K` with `d(s₀, t s₀) ≥ R`.  Lemma 3.6, applied to
  the pairs `(s₀, t s₀)` and `(s₀, t⁻¹ s₀)`, leaves some `a ∈ A(s₀)` moving both
  `t s₀` and `t⁻¹ s₀` by more than `d(s₀, t s₀) + ε`.  Lemma 3.5, for `g = a`,
  `h = t a t⁻¹`, `x = s₀`, `y = t s₀`, makes `a · t a t⁻¹` loxodromic.

## Manuscript status

Infrastructure for the limit-set spelling of acylindrical hyperbolicity used in
`sec:torsion-free` (Osin's Definition 1.3 with Theorem 1.1); certifies no printed
sentence on its own.
-/

namespace GroupApproximation
namespace GGT
namespace OsinClassification

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

section Geodesic

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

omit [Group G] in
/-- A set that is not finite of size at most `k` has a finite subset of size
`k + 1`. -/
theorem exists_finite_subset_ncard_eq {s : Set G} {k : ℕ}
    (h : ¬ (s.Finite ∧ s.ncard ≤ k)) : ∃ t ⊆ s, t.Finite ∧ t.ncard = k + 1 := by
  by_cases hfin : s.Finite
  · have hgt : k < s.ncard := by
      by_contra hle
      exact h ⟨hfin, by omega⟩
    have hk : ((k + 1 : ℕ) : ℕ∞) ≤ s.encard := by
      rw [← hfin.cast_ncard_eq]
      exact_mod_cast Nat.succ_le_of_lt hgt
    obtain ⟨t, hts, htk⟩ := Set.exists_subset_encard_eq hk
    have htfin : t.Finite := Set.finite_of_encard_eq_coe htk
    refine ⟨t, hts, htfin, ?_⟩
    have hcast := htfin.cast_ncard_eq
    rw [htk] at hcast
    exact_mod_cast hcast
  · obtain ⟨t, hts, htfin, htk⟩ := Set.Infinite.exists_subset_ncard_eq hfin (k + 1)
    exact ⟨t, hts, htfin, htk⟩

/-- **Osin's Theorem 1.1, subgroup form, at a geodesic space.**  For an
acylindrical isometric action on a geodesic hyperbolic space, every subgroup
with an unbounded orbit contains a loxodromic element. -/
theorem hasLoxodromicOfUnbounded_of_geodesic {δ : ℝ} (hδ : IsHyperbolicSpace δ X)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) (x : X) : Elementary.HasLoxodromicOfUnbounded G x := by
  intro K hunb
  have hδ0 := nonneg_delta hδ x
  by_cases hup : ∀ ε : ℝ, ∃ N : ℕ, ∀ s : X,
      (quasiStabilizer K ε s).Finite ∧ (quasiStabilizer K ε s).ncard ≤ N
  · exact exists_loxodromic_of_uniformlyProper hδ hgeo hiso hup hunb
  · -- a radius at which quasi-stabilizers are arbitrarily large
    obtain ⟨C₀, hC₀⟩ : ∃ ε : ℝ, ∀ N : ℕ, ∃ s : X,
        ¬ ((quasiStabilizer K ε s).Finite ∧ (quasiStabilizer K ε s).ncard ≤ N) := by
      by_contra hne
      apply hup
      intro ε
      by_contra hno
      apply hne
      refine ⟨ε, fun N => ?_⟩
      by_contra hs
      apply hno
      refine ⟨N, fun s => ?_⟩
      by_contra hs'
      exact hs ⟨s, hs'⟩
    have hC0 : 0 ≤ max C₀ 0 := le_max_right _ _
    have hsubC : ∀ s : X, quasiStabilizer K C₀ s ⊆ quasiStabilizer K (max C₀ 0) s := by
      rintro s c ⟨hcK, hcd⟩
      exact ⟨hcK, le_trans hcd (le_max_left _ _)⟩
    obtain ⟨R, N, hRN⟩ := far_quasiStabilizer_finite hδ hδ0 hgeo hiso hacy
      (ε := 2 * max C₀ 0 + (2 * δ + 1)) (by linarith)
    obtain ⟨s₀, hs₀⟩ := hC₀ (2 * N)
    obtain ⟨T, hTs, hTfin, hTcard⟩ := exists_finite_subset_ncard_eq hs₀
    have hTsub : T ⊆ quasiStabilizer K (max C₀ 0) s₀ := hTs.trans (hsubC s₀)
    -- an element of `K` moving `s₀` far
    obtain ⟨t, htK, htfar⟩ : ∃ t ∈ K, R ≤ dist s₀ (t • s₀) := by
      by_contra hb
      push Not at hb
      apply hunb
      refine ⟨R + 2 * dist x s₀, fun c hc => ?_⟩
      have h1 := dist_triangle x s₀ (c • x)
      have h2 := dist_triangle s₀ (c • s₀) (c • x)
      have h3 : dist (c • s₀) (c • x) = dist s₀ x := hiso c s₀ x
      have h4 := hb c hc
      rw [dist_comm s₀ x] at h3
      linarith
    have htinv : dist s₀ (t⁻¹ • s₀) = dist s₀ (t • s₀) := PNaive.dist_inv_smul hiso t s₀
    obtain ⟨hB1fin, hB1card⟩ := hRN s₀ (t • s₀) htfar
    obtain ⟨hB2fin, hB2card⟩ := hRN s₀ (t⁻¹ • s₀) (by rw [htinv]; exact htfar)
    -- some element of `T` escapes both exceptional sets of Lemma 3.6
    obtain ⟨a, haT, haB⟩ : ∃ a ∈ T,
        a ∉ {g : G | dist s₀ (g • s₀) ≤ 2 * max C₀ 0 + (2 * δ + 1) ∧
            dist (t • s₀) (g • t • s₀) ≤ dist s₀ (t • s₀) + (2 * max C₀ 0 + (2 * δ + 1))} ∪
          {g : G | dist s₀ (g • s₀) ≤ 2 * max C₀ 0 + (2 * δ + 1) ∧
            dist (t⁻¹ • s₀) (g • t⁻¹ • s₀) ≤
              dist s₀ (t⁻¹ • s₀) + (2 * max C₀ 0 + (2 * δ + 1))} := by
      by_contra hall
      push Not at hall
      have h1 := Set.ncard_le_ncard hall (hB1fin.union hB2fin)
      have h2 := Set.ncard_union_le
        {g : G | dist s₀ (g • s₀) ≤ 2 * max C₀ 0 + (2 * δ + 1) ∧
          dist (t • s₀) (g • t • s₀) ≤ dist s₀ (t • s₀) + (2 * max C₀ 0 + (2 * δ + 1))}
        {g : G | dist s₀ (g • s₀) ≤ 2 * max C₀ 0 + (2 * δ + 1) ∧
          dist (t⁻¹ • s₀) (g • t⁻¹ • s₀) ≤
            dist s₀ (t⁻¹ • s₀) + (2 * max C₀ 0 + (2 * δ + 1))}
      omega
    obtain ⟨haK, hax⟩ := hTsub haT
    have hfar1 : dist s₀ (t • s₀) + (2 * max C₀ 0 + (2 * δ + 1)) <
        dist (t • s₀) (a • t • s₀) := by
      by_contra hle
      push Not at hle
      exact haB (Or.inl ⟨by linarith, hle⟩)
    have hfar2 : dist s₀ (t⁻¹ • s₀) + (2 * max C₀ 0 + (2 * δ + 1)) <
        dist (t⁻¹ • s₀) (a • t⁻¹ • s₀) := by
      by_contra hle
      push Not at hle
      exact haB (Or.inr ⟨by linarith, hle⟩)
    -- Lemma 3.5 for `a` and its conjugate `t a t⁻¹`
    have hhy : dist (t • s₀) ((t * a * t⁻¹) • t • s₀) ≤ max C₀ 0 := by
      have e : (t * a * t⁻¹) • t • s₀ = t • a • s₀ := by
        rw [smul_smul, smul_smul, inv_mul_cancel_right]
      rw [e, hiso t]
      exact hax
    have hhx : dist s₀ (t • s₀) + 2 * max C₀ 0 + (2 * δ + 1) ≤
        dist s₀ ((t * a * t⁻¹) • s₀) := by
      have e1 : t⁻¹ • (t * a * t⁻¹) • s₀ = a • t⁻¹ • s₀ := by
        rw [smul_smul, smul_smul]
        congr 1
        group
      have e : dist s₀ ((t * a * t⁻¹) • s₀) = dist (t⁻¹ • s₀) (a • t⁻¹ • s₀) := by
        rw [← e1, hiso t⁻¹]
      rw [e]
      linarith
    have hlox := isLoxodromic_mul_of_quasiFixed hδ hiso (K := 2 * δ + 1) (C := max C₀ 0)
      (by linarith) (g := a) (h := t * a * t⁻¹) (x := s₀) (y := t • s₀) hax hhy hhx
      (by linarith)
    exact ⟨a * (t * a * t⁻¹), K.mul_mem haK (K.mul_mem (K.mul_mem htK haK) (K.inv_mem htK)),
      isLoxodromic_of_isLoxodromic hiso hlox⟩

end Geodesic

/-- **Osin's Theorem 1.1, subgroup form, at Hull's Cayley graph.**  Proved in
the geodesic realisation of `Γ(G, A)` and pulled back along the vertex inclusion,
which has bounded additive distortion and dense image. -/
theorem hasLoxodromicOfUnbounded_cayley {G : Type u} [Group G] (A : HullGeneratingSet G) :
    Elementary.HasLoxodromicOfUnbounded G (Cayley.base A.alphabet) := by
  obtain ⟨M⟩ := CayleyGeodesicModel.hasGeodesicModel_of_hullGeneratingSet A
  have hacyW : IsAcylindrical G M.W :=
    isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric
      A.acylindrical
  intro K hunb
  have hunbW : ¬ ∃ B : ℝ, ∀ c ∈ K,
      dist (M.iota (Cayley.base A.alphabet)) (c • M.iota (Cayley.base A.alphabet)) ≤ B := by
    rintro ⟨B, hB⟩
    apply hunb
    refine ⟨B + M.distortion, fun c hc => ?_⟩
    have h1 := M.hasAdditiveDistortion (Cayley.base A.alphabet) (c • Cayley.base A.alphabet)
    rw [M.equivariant c] at h1
    have h2 := (abs_le.mp h1).1
    have h3 := hB c hc
    linarith
  obtain ⟨c, hcK, hlox⟩ := hasLoxodromicOfUnbounded_of_geodesic M.hyperbolic M.geodesic
    M.isometric hacyW _ K hunbW
  exact ⟨c, hcK, isLoxodromic_of_map M.distortion_nonneg M.hasAdditiveDistortion
    M.equivariant hlox⟩

end OsinClassification
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.OsinClassification.exists_finite_subset_ncard_eq
#audit_axioms GroupApproximation.GGT.OsinClassification.hasLoxodromicOfUnbounded_of_geodesic
#audit_axioms GroupApproximation.GGT.OsinClassification.hasLoxodromicOfUnbounded_cayley
