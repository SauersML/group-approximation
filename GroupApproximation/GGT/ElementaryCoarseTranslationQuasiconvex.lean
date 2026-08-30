import GroupApproximation.GGT.ElementaryCoarseTranslationProperAction
import GroupApproximation.GGT.ElementaryMorseChord

/-!
# Quasiconvexity of an elementary-closure orbit

The uniform coarse-translation conclusion of DGO Lemma 6.5 also supplies
condition (b) in DGO Theorem 4.42.  An element of `E(h)` sends the basepoint
within a uniform distance of a power of `h`.  To avoid assuming that the whole
ambient space is geodesic, append that element's orbit point to the finite
power-orbit chain.  The appended chain still has uniform step and progress
constants, and `ElementaryMorse.exists_bound_chord_near_chain` applies to the
particular geodesic occurring in `IsQuasiconvexOrbitAt`.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

namespace ElementaryMorse

universe v

variable {X : Type v} [PseudoMetricSpace X]

/-- Append one point after the first `N + 1` entries of a chain. -/
def appendPoint (y : ℕ → X) (N : ℕ) (z : X) (i : ℕ) : X :=
  if i ≤ N then y i else z

/-- A bounded perturbation of the last endpoint can be appended to a
quasi-geodesic chain without losing uniform Morse control. -/
theorem exists_bound_chord_near_chain_append_endpoint {δ D l B E : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hD0 : 0 ≤ D)
    (hl : 0 < l) (hB0 : 0 ≤ B) (hE0 : 0 ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : ℕ → X) (N : ℕ) (z : X),
      (∀ i, i < N → dist (y i) (y (i + 1)) ≤ D) →
      (∀ i j, i ≤ j → j ≤ N →
        l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j)) →
      dist (y N) z ≤ E →
      ∀ (L : ℝ), 0 ≤ L → ∀ (f : ℝ → X), IsGeodesicSegment f 0 L →
        f 0 = y 0 → f L = z → ∀ t ∈ Set.Icc (0 : ℝ) L,
          (∃ i, i ≤ N ∧ dist (y i) (f t) ≤ K) ∨ dist z (f t) ≤ K := by
  have hmax0 : 0 ≤ max D E := le_max_of_le_left hD0
  have hslack0 : 0 ≤ B + E + l := by linarith
  obtain ⟨K, hK0, hK⟩ :=
    exists_bound_chord_near_chain hδ hδ0 hmax0 hl hslack0
  refine ⟨K, hK0, ?_⟩
  intro y N z hedge hprog hend L hL f hf hf0 hfL t ht
  let y' : ℕ → X := appendPoint y N z
  have hy'_le : ∀ i, i ≤ N → y' i = y i := by
    intro i hi
    simp [y', appendPoint, hi]
  have hy'_last : y' (N + 1) = z := by
    simp [y', appendPoint]
  have hedge' : ∀ i, i < N + 1 →
      dist (y' i) (y' (i + 1)) ≤ max D E := by
    intro i hi
    by_cases hiN : i < N
    · rw [hy'_le i hiN.le, hy'_le (i + 1) hiN]
      exact (hedge i hiN).trans (le_max_left _ _)
    · have hiN' : i = N := by omega
      subst i
      rw [hy'_le N le_rfl, hy'_last]
      exact hend.trans (le_max_right _ _)
  have hprog' : ∀ i j, i ≤ j → j ≤ N + 1 →
      l * ((j - i : ℕ) : ℝ) - (B + E + l) ≤ dist (y' i) (y' j) := by
    intro i j hij hj
    by_cases hjN : j ≤ N
    · rw [hy'_le i (hij.trans hjN), hy'_le j hjN]
      have h := hprog i j hij hjN
      linarith
    · have hjlast : j = N + 1 := by omega
      subst hjlast
      by_cases hiN : i ≤ N
      · rw [hy'_le i hiN, hy'_last]
        have hchain := hprog i N hiN le_rfl
        have htri := dist_triangle (y i) z (y N)
        have hdist : dist z (y N) ≤ E := by
          rw [dist_comm]
          exact hend
        have hsub : N + 1 - i = (N - i) + 1 := by omega
        rw [hsub, Nat.cast_add, Nat.cast_one]
        linarith
      · have hi : i = N + 1 := by omega
        subst hi
        rw [hy'_last, dist_self, Nat.sub_self, Nat.cast_zero]
        linarith
  obtain ⟨i, hi, hnear⟩ := hK y' (N + 1) hedge' hprog' L hL f hf
    (by rw [hy'_le 0 (Nat.zero_le N)]; exact hf0) (by rw [hy'_last]; exact hfL) t ht
  by_cases hiN : i ≤ N
  · exact Or.inl ⟨i, hiN, by rwa [hy'_le i hiN] at hnear⟩
  · have hilast : i = N + 1 := by omega
    subst hilast
    exact Or.inr (by rwa [hy'_last] at hnear)

end ElementaryMorse

namespace Elementary

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- The elementary-closure orbit is uniformly close to the power orbit at the
basepoint.  This is the only consequence of coarse translation used for
quasiconvexity. -/
def ElementaryClosureOrbitClose (h : G) (x : X) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ g : G, g ∈ elementaryClosure h →
    ∃ c : ℤ, dist ((h ^ c) • x) (g • x) ≤ K

/-- Uniform coarse translation implies uniform closeness of the two orbits by
specialising at exponent zero. -/
theorem elementaryClosureOrbitClose_of_coarseTranslation
    {h : G} {x : X} (hlox : IsLoxodromic h x)
    (hct : ElementaryClosureCoarseTranslation G x) :
    ElementaryClosureOrbitClose h x := by
  obtain ⟨K, hK, hall⟩ := hct h hlox
  refine ⟨K, hK, ?_⟩
  intro g hg
  obtain ⟨e, c, _he, hc⟩ := hall g hg
  refine ⟨c, ?_⟩
  have hzero : dist (g • x) ((h ^ c) • x) ≤ K := by
    simpa using hc 0
  rwa [dist_comm] at hzero

/-- Uniform coarse translation makes the elementary-closure orbit
quasiconvex.  Only the geodesic segment appearing in the definition is used;
the ambient space need not be a geodesic space. -/
theorem isQuasiconvexOrbitAt_elementaryClosure_of_orbitClose
    {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x)
    (hclose : ElementaryClosureOrbitClose h x) :
    IsQuasiconvexOrbitAt (elementaryClosure h) x := by
  obtain ⟨K, hK0, hclose⟩ := hclose
  have hloxinv : IsLoxodromic h⁻¹ x := isLoxodromic_inv hiso hlox
  obtain ⟨l₁, hl₁, B₁, hB₁, hlin₁⟩ := hlox
  obtain ⟨l₂, hl₂, B₂, hB₂, hlin₂⟩ := hloxinv
  obtain ⟨σ₁, hσ₁, hnear₁⟩ :=
    ElementaryMorse.exists_bound_chord_near_chain_append_endpoint
      (D := dist x (h • x)) (l := l₁) (B := B₁) (E := K)
      hδ hδ0 dist_nonneg hl₁ hB₁ hK0
  obtain ⟨σ₂, hσ₂, hnear₂⟩ :=
    ElementaryMorse.exists_bound_chord_near_chain_append_endpoint
      (D := dist x (h⁻¹ • x)) (l := l₂) (B := B₂) (E := K)
      hδ hδ0 dist_nonneg hl₂ hB₂ hK0
  refine ⟨max σ₁ σ₂, le_max_of_le_left hσ₁, ?_⟩
  intro a b ha hb f hf hf0 hfL t ht
  let q : G := a⁻¹ * b
  have hqE : q ∈ elementaryClosure h := by
    exact (elementaryClosure h).mul_mem ((elementaryClosure h).inv_mem ha) hb
  have hlen : dist (a • x) (b • x) = dist x (q • x) := by
    have hm := hiso a⁻¹ (a • x) (b • x)
    simpa only [q, ← mul_smul, inv_mul_cancel, one_smul] using hm.symm
  let f' : ℝ → X := fun s => a⁻¹ • f s
  have hf' : IsGeodesicSegment f' 0 (dist x (q • x)) := by
    rw [← hlen]
    intro s hs r hr
    dsimp [f']
    rw [hiso]
    exact hf s hs r hr
  have hf'0 : f' 0 = x := by
    dsimp [f']
    rw [hf0, ← mul_smul, inv_mul_cancel, one_smul]
  have hf'L : f' (dist x (q • x)) = q • x := by
    dsimp [f']
    rw [← hlen, hfL, ← mul_smul]
  obtain ⟨c, hend⟩ := hclose q hqE
  rcases Int.natAbs_eq c with hc | hc
  · let y : ℕ → X := ElementaryMorse.orbitChain h x 0
    have hedge : ∀ i, i < c.natAbs →
        dist (y i) (y (i + 1)) ≤ dist x (h • x) := by
      intro i _
      exact le_of_eq (ElementaryMorse.orbitChain_edge hiso h x 0 i)
    have hprog : ∀ i j, i ≤ j → j ≤ c.natAbs →
        l₁ * ((j - i : ℕ) : ℝ) - B₁ ≤ dist (y i) (y j) := by
      intro i j hij _
      exact ElementaryMorse.orbitChain_prog hiso hlin₁ 0 hij
    have hy0 : y 0 = x := ElementaryMorse.orbitChain_self h x 0
    have hyN : y c.natAbs = (h ^ c) • x := by
      have hc' : (c.natAbs : ℤ) = c := hc.symm
      unfold y ElementaryMorse.orbitChain
      rw [Nat.cast_zero, sub_zero, hc']
    obtain hnear := hnear₁ y c.natAbs (q • x) hedge hprog
      (by rwa [hyN]) (dist x (q • x)) dist_nonneg f' hf'
      (by rw [hy0]; exact hf'0) hf'L t
      (by rwa [← hlen])
    rcases hnear with ⟨i, _hi, hi⟩ | hq
    · refine ⟨a * h ^ (i : ℤ), ?_, ?_⟩
      · exact (elementaryClosure h).mul_mem ha
          (Subgroup.zpow_mem _ (self_mem_elementaryClosure h) i)
      · have htranslate := hiso a (f' t) ((h ^ (i : ℤ)) • x)
        have hy : y i = (h ^ (i : ℤ)) • x := by
          unfold y ElementaryMorse.orbitChain
          rw [Nat.cast_zero, sub_zero]
        rw [hy] at hi
        calc
          dist (f t) ((a * h ^ (i : ℤ)) • x) =
              dist (a • f' t) (a • ((h ^ (i : ℤ)) • x)) := by
                simp [f', ← mul_smul]
          _ = dist (f' t) ((h ^ (i : ℤ)) • x) := htranslate
          _ ≤ σ₁ := by rwa [dist_comm]
          _ ≤ max σ₁ σ₂ := le_max_left _ _
    · refine ⟨b, hb, ?_⟩
      have htranslate := hiso a (f' t) (q • x)
      calc
        dist (f t) (b • x) = dist (a • f' t) (a • (q • x)) := by
          simp [f', q, ← mul_smul]
        _ = dist (f' t) (q • x) := htranslate
        _ ≤ σ₁ := by rwa [dist_comm]
        _ ≤ max σ₁ σ₂ := le_max_left _ _
  · let y : ℕ → X := ElementaryMorse.orbitChain h⁻¹ x 0
    have hedge : ∀ i, i < c.natAbs →
        dist (y i) (y (i + 1)) ≤ dist x (h⁻¹ • x) := by
      intro i _
      exact le_of_eq (ElementaryMorse.orbitChain_edge hiso h⁻¹ x 0 i)
    have hprog : ∀ i j, i ≤ j → j ≤ c.natAbs →
        l₂ * ((j - i : ℕ) : ℝ) - B₂ ≤ dist (y i) (y j) := by
      intro i j hij _
      exact ElementaryMorse.orbitChain_prog hiso hlin₂ 0 hij
    have hy0 : y 0 = x := ElementaryMorse.orbitChain_self h⁻¹ x 0
    have hyN : y c.natAbs = (h ^ c) • x := by
      have hc' : -(c.natAbs : ℤ) = c := hc.symm
      unfold y ElementaryMorse.orbitChain
      rw [Nat.cast_zero, sub_zero, inv_zpow, ← zpow_neg, hc']
    obtain hnear := hnear₂ y c.natAbs (q • x) hedge hprog
      (by rwa [hyN]) (dist x (q • x)) dist_nonneg f' hf'
      (by rw [hy0]; exact hf'0) hf'L t
      (by rwa [← hlen])
    rcases hnear with ⟨i, _hi, hi⟩ | hq
    · refine ⟨a * h⁻¹ ^ (i : ℤ), ?_, ?_⟩
      · exact (elementaryClosure h).mul_mem ha
          (Subgroup.zpow_mem _ ((elementaryClosure h).inv_mem
            (self_mem_elementaryClosure h)) i)
      · have htranslate := hiso a (f' t) ((h⁻¹ ^ (i : ℤ)) • x)
        have hy : y i = (h⁻¹ ^ (i : ℤ)) • x := by
          unfold y ElementaryMorse.orbitChain
          rw [Nat.cast_zero, sub_zero]
        rw [hy] at hi
        calc
          dist (f t) ((a * h⁻¹ ^ (i : ℤ)) • x) =
              dist (a • f' t) (a • ((h⁻¹ ^ (i : ℤ)) • x)) := by
                simp [f', ← mul_smul]
          _ = dist (f' t) ((h⁻¹ ^ (i : ℤ)) • x) := htranslate
          _ ≤ σ₂ := by rwa [dist_comm]
          _ ≤ max σ₁ σ₂ := le_max_right _ _
    · refine ⟨b, hb, ?_⟩
      have htranslate := hiso a (f' t) (q • x)
      calc
        dist (f t) (b • x) = dist (a • f' t) (a • (q • x)) := by
          simp [f', q, ← mul_smul]
        _ = dist (f' t) (q • x) := htranslate
        _ ≤ σ₂ := by rwa [dist_comm]
        _ ≤ max σ₁ σ₂ := le_max_right _ _

/-- The coarse-translation form implies quasiconvexity through uniform orbit
closeness. -/
theorem isQuasiconvexOrbitAt_elementaryClosure_of_coarseTranslation
    {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x)
    (hct : ElementaryClosureCoarseTranslation G x) :
    IsQuasiconvexOrbitAt (elementaryClosure h) x :=
  isQuasiconvexOrbitAt_elementaryClosure_of_orbitClose hδ hδ0 hiso hlox
    (elementaryClosureOrbitClose_of_coarseTranslation hlox hct)

end Elementary
end GGT
end GroupApproximation
