import GroupApproximation.GGT.ElementaryCoarseTranslationProper

/-!
# Properness of the elementary-closure action

Uniform coarse translation and WPD imply that the elementary closure acts
properly at the basepoint.  This is condition (c) used in DGO's application of
the projection-complex theorem to `E(g)`.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- Only finitely many integer powers of a loxodromic element move the
basepoint by a bounded amount. -/
theorem finite_zpow_displacement (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x) (R : ℝ) :
    {c : ℤ | dist x ((h ^ c) • x) ≤ R}.Finite := by
  let tau := stableTranslation h x
  have htau : 0 < tau := stableTranslation_pos_of_isLoxodromic hiso hlox
  let C : ℕ := ⌈max 0 (R / tau)⌉₊
  refine (Set.finite_Icc (-(C : ℤ)) (C : ℤ)).subset ?_
  intro c hc
  have hlow := mul_le_dist_zpow hiso h x c
  have habs : |(c : ℝ)| ≤ R / tau := by
    rw [le_div_iff₀ htau]
    rw [mul_comm]
    exact hlow.trans hc
  have hC : R / tau ≤ (C : ℝ) := by
    exact le_trans (le_max_right 0 (R / tau)) (Nat.le_ceil _)
  have habsC : |(c : ℝ)| ≤ (C : ℝ) := habs.trans hC
  have hinterval := (abs_le.mp habsC)
  constructor
  · exact_mod_cast hinterval.1
  · exact_mod_cast hinterval.2

/-- Preserving coarse translations that move the basepoint a bounded amount
form a finite set. -/
theorem finite_preserving_movers (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hwpd : IsWPDAt h x) (hlox : IsLoxodromic h x) {K : ℝ} (hK : 0 ≤ K)
    (eps : ℝ) :
    {g : G | (∃ c : ℤ, ∀ m : ℤ,
        dist ((g * h ^ m) • x) ((h ^ (m + c)) • x) ≤ K) ∧
      dist x (g • x) ≤ eps}.Finite := by
  obtain ⟨F, hFfin, hF⟩ :=
    exists_finite_transversal_of_coarseTranslation hiso hwpd hK
  refine Set.Finite.subset
    (hFfin.biUnion fun f _ =>
      (finite_zpow_displacement hiso hlox (eps + dist x (f • x))).image
        (fun c : ℤ => h ^ c * f)) ?_
  rintro g ⟨hgpres, hgmove⟩
  obtain ⟨c, f, hfF, hgf⟩ := hF g hgpres
  have hpow : dist x ((h ^ c) • x) ≤ eps + dist x (f • x) := by
    have htri := dist_triangle x (g • x) ((h ^ c) • x)
    have heq : dist (g • x) ((h ^ c) • x) = dist (f • x) x := by
      rw [hgf]
      have hm := hiso (h ^ c) (f • x) x
      simpa only [← mul_smul] using hm
    calc
      dist x ((h ^ c) • x) ≤ dist x (g • x) +
          dist (g • x) ((h ^ c) • x) := htri
      _ = dist x (g • x) + dist x (f • x) := by
        rw [heq]
        congr 1
        exact dist_comm _ _
      _ ≤ eps + dist x (f • x) := add_le_add hgmove le_rfl
  refine Set.mem_iUnion.mpr ⟨f, Set.mem_iUnion.mpr ⟨hfF, ?_⟩⟩
  exact ⟨c, hpow, hgf.symm⟩

/-- **The elementary closure acts properly at the basepoint.**  The preserving
part is finite by WPD.  If reversing elements occur, fix one of them; the
product of any other reversing element with its inverse is preserving, with
twice the error, so the reversing part is one translate of another finite set. -/
theorem actsProperlyAt_elementaryClosure_of_coarseTranslation
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hwpd : IsWPDAt h x) (hlox : IsLoxodromic h x)
    (hct : ElementaryClosureCoarseTranslation G x) :
    ActsProperlyAt (elementaryClosure h) x := by
  obtain ⟨K, hK, hall⟩ := hct h hlox
  intro eps
  let P : Set G := {g : G | ∃ c : ℤ, ∀ m : ℤ,
    dist ((g * h ^ m) • x) ((h ^ (m + c)) • x) ≤ K}
  let N : Set G := {g : G | ∃ c : ℤ, ∀ m : ℤ,
    dist ((g * h ^ m) • x) ((h ^ (-m + c)) • x) ≤ K}
  have hPfin : {g : G | g ∈ P ∧ dist x (g • x) ≤ eps}.Finite := by
    exact finite_preserving_movers hiso hwpd hlox hK eps
  by_cases hNempty : {g : G | g ∈ N ∧ dist x (g • x) ≤ eps}.Nonempty
  · obtain ⟨r, hrN, hrmove⟩ := hNempty
    obtain ⟨cr, hr⟩ := hrN
    have h2K : 0 ≤ K + K := add_nonneg hK hK
    have hQfin : {q : G | (∃ c : ℤ, ∀ m : ℤ,
          dist ((q * h ^ m) • x) ((h ^ (m + c)) • x) ≤ K + K) ∧
        dist x (q • x) ≤ eps + eps}.Finite :=
      finite_preserving_movers hiso hwpd hlox h2K (eps + eps)
    have hNfin : {g : G | g ∈ N ∧ dist x (g • x) ≤ eps}.Finite := by
      refine Set.Finite.subset (hQfin.image (fun q : G => q * r)) ?_
      rintro a ⟨haN, hamove⟩
      obtain ⟨ca, ha⟩ := haN
      have haPres := coarsePreserving_mul_inv_of_reversing hiso ha hr
      have hqmove : dist x ((a * r⁻¹) • x) ≤ eps + eps := by
        calc
          dist x ((a * r⁻¹) • x) ≤ dist x (a • x) +
              dist (a • x) ((a * r⁻¹) • x) := dist_triangle _ _ _
          _ = dist x (a • x) + dist x (r • x) := by
            have hm := hiso a x (r⁻¹ • x)
            have hi := hiso r⁻¹ (r • x) x
            simp only [← mul_smul, inv_mul_cancel, one_smul] at hi
            have hm' : dist (a • x) ((a * r⁻¹) • x) =
                dist x (r⁻¹ • x) := by
              simpa only [← mul_smul] using hm
            rw [hm', hi]
            congr 1
            exact dist_comm _ _
          _ ≤ eps + eps := add_le_add hamove hrmove
      refine ⟨a * r⁻¹, ⟨⟨ca - cr, by
        intro m
        simpa [add_assoc] using haPres m⟩, hqmove⟩, ?_⟩
      group
    refine (hPfin.union hNfin).subset ?_
    rintro g ⟨hgE, hgmove⟩
    obtain ⟨e, c, he, hgc⟩ := hall g hgE
    rcases he with rfl | rfl
    · exact Or.inl ⟨⟨c, by simpa using hgc⟩, hgmove⟩
    · exact Or.inr ⟨⟨c, by simpa using hgc⟩, hgmove⟩
  · have hNfin : {g : G | g ∈ N ∧ dist x (g • x) ≤ eps}.Finite :=
      Set.not_nonempty_iff_eq_empty.mp hNempty ▸ Set.finite_empty
    refine (hPfin.union hNfin).subset ?_
    rintro g ⟨hgE, hgmove⟩
    obtain ⟨e, c, he, hgc⟩ := hall g hgE
    rcases he with rfl | rfl
    · exact Or.inl ⟨⟨c, by simpa using hgc⟩, hgmove⟩
    · exact Or.inr ⟨⟨c, by simpa using hgc⟩, hgmove⟩

end Elementary
end GGT
end GroupApproximation
