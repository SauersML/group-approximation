import GroupApproximation.GGT.ElementaryBowditch
import GroupApproximation.GGT.ElementaryIndependence

/-!
# Osin's Lemma 7.1 for normal subgroups, closed

`ElementaryBowditch.actsNonElementarily_of_isSNormal_of_normal_of_torsionFree`
proves Osin's Lemma 7.1 for a normal `s`-normal subgroup of a torsion-free
group from three residuals: `CentralizerOrbitNearAxis`, `EscapingIsLoxodromic`
and `IndependentOfNoCommonZpow`.  The first and third are theorems now
(`ElementaryMorseOrbit`, `ElementaryIndependence`).  The second — Bowditch's
dichotomy — is used in that chain at exactly one lemma,
`isLoxodromic_of_commute_of_escapingIsLoxodromic`: an infinite-order element
commuting with a loxodromic element is loxodromic.  That lemma does not need
the dichotomy.  It follows from the centralizer theorem and acylindricity:

* `CentralizerOrbitNearAxis` puts every power `cᵏx` within `K` of the
  `q`-orbit, so each `cᵏ` has a partner exponent on the axis of `q`;
* `isEscaping_of_commutes_of_not_isOfFinOrder` (finiteness of centralizer
  balls) makes the `c`-orbit escape, so exponents spaced by a fixed `S` have
  orbit points more than `2K + 2` apart and hence distinct partners;
* the commuting relation makes the second basepoint `qᴹx` free, exactly as in
  `exists_common_zpow_of_commute_of_orbitNearAxis`, and the acylindrical
  pigeonhole produces a common nonzero power `cᵖ = qʳ`, which makes `c`
  loxodromic (`isLoxodromic_of_common_zpow`).

This module re-runs the normal-case chain with that lemma in place of the
dichotomy and closes the manuscript's statement at Hull's Cayley graph:
`osinLemma71_closed` has exactly the type of `TheoremCAssembly.osinLemma71`.

## Status

**Not compiled**, written while builds were frozen.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X] [MulAction G X]

/-! ## An infinite-order element commuting with a loxodromic one is loxodromic -/

/-- **The centralizer of a loxodromic element has no infinite-order
non-loxodromic element**, from the Morse theorem and acylindricity alone. -/
theorem isLoxodromic_of_commute_of_orbitNearAxis
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x) {q c : G}
    (hq : IsLoxodromic q x) (hcq : Commute c q) (hcfin : ¬ IsOfFinOrder c) :
    IsLoxodromic c x := by
  obtain ⟨K, hK0, hK⟩ := hnear q hq
  have hε : (0 : ℝ) < K + 1 := by linarith
  obtain ⟨R, N, hRN⟩ :=
    acylindrical_common_power_of_two_orbit_fellow_travel hiso hacy hε
  -- a second basepoint, far out along the axis of `q`
  have hev := hq.isEscaping.eventually_ge_atTop R
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  have hfar : R ≤ dist x ((q ^ M) • x) := hM M le_rfl
  -- the `c`-orbit escapes, which spaces the exponents
  have hesc : IsEscaping c x :=
    isEscaping_of_commutes_of_not_isOfFinOrder hiso hacy hq hcq hcfin
  have hev' := hesc.eventually_gt_atTop (2 * (K + 1))
  rw [Filter.eventually_atTop] at hev'
  obtain ⟨e₀, he₀⟩ := hev'
  obtain ⟨S, hS⟩ : ∃ S : ℕ, S = e₀ + 1 := ⟨_, rfl⟩
  have hSpos : 0 < S := by omega
  obtain ⟨A, hA⟩ : ∃ A : Fin (N + 1) → ℤ, ∀ i, A i = (S : ℤ) * i.val :=
    ⟨_, fun _ => rfl⟩
  have hAinj : Function.Injective A := by
    intro i j h
    rw [hA, hA] at h
    have hS0 : (S : ℤ) ≠ 0 := by exact_mod_cast hSpos.ne'
    have h2 : (i.val : ℤ) = j.val := mul_left_cancel₀ hS0 h
    exact Fin.ext (by exact_mod_cast h2)
  choose B hB using fun i : Fin (N + 1) => hK c hcq (A i)
  -- the partners are distinct, because the `c`-exponents are spaced
  have hBinj : Function.Injective B := by
    intro i j hij
    by_contra hne
    have h1 := hB i
    have h2 := hB j
    have hswap : dist ((q ^ (B i)) • x) ((c ^ (A j)) • x)
        = dist ((c ^ (A j)) • x) ((q ^ (B j)) • x) := by
      rw [dist_comm, hij]
    have htri :=
      dist_triangle ((c ^ (A i)) • x) ((q ^ (B i)) • x) ((c ^ (A j)) • x)
    rw [hswap] at htri
    have horbit := dist_zpow_orbit hiso c x (A i) (A j)
    rw [dist_zpow_natAbs hiso] at horbit
    have hnat : S ≤ (A j - A i).natAbs := by
      rw [hA, hA, ← mul_sub, Int.natAbs_mul]
      have hne' : ((j.val : ℤ) - i.val).natAbs ≠ 0 := by
        intro h0
        apply hne
        exact Fin.ext (by omega)
      have h1' : (S : ℤ).natAbs = S := by omega
      rw [h1']
      calc S = S * 1 := (Nat.mul_one S).symm
        _ ≤ S * ((j.val : ℤ) - i.val).natAbs :=
          Nat.mul_le_mul_left S (Nat.one_le_iff_ne_zero.mpr hne')
    have hfar' := he₀ _ (by omega : e₀ ≤ (A j - A i).natAbs)
    linarith
  -- the matched pairs, at both basepoints
  have hclose : ∀ i : Fin (N + 1),
      dist ((c ^ (A i)) • x) ((q ^ (B i)) • x) ≤ K + 1 ∧
        dist ((c ^ (A i)) • ((q ^ M) • x)) ((q ^ (B i)) • ((q ^ M) • x))
          ≤ K + 1 := by
    intro i
    refine ⟨by linarith [hB i], ?_⟩
    rw [dist_smul_of_commute_translate hiso hcq (A i) (B i) M x]
    linarith [hB i]
  obtain ⟨i, j, -, hpne, hrne, hpow⟩ :=
    hRN x ((q ^ M) • x) hfar c q A B hAinj hBinj hclose
  exact isLoxodromic_of_common_zpow hiso hq hrne hpne hpow.symm

/-! ## The chain, without the dichotomy -/

/-- `exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder` with the
dichotomy replaced by the centralizer lemma above. -/
theorem exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder'
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x)
    {g c : G} (hg : IsLoxodromic g x) (hc : c ∈ elementaryClosure g)
    (hcfin : ¬ IsOfFinOrder c) :
    ∃ i m : ℤ, i ≠ 0 ∧ m ≠ 0 ∧ g ^ i = c ^ m := by
  obtain ⟨n, hn, hcomm⟩ :=
    exists_ne_zero_commute_sq_of_mem_elementaryClosure hiso hg hc
  have hgn : IsLoxodromic (g ^ n) x := isLoxodromic_zpow hiso hg hn
  have hc2fin : ¬ IsOfFinOrder (c * c) := by
    intro hfin
    obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    refine hcfin (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * k, by omega, ?_⟩)
    rw [pow_mul, pow_two]
    exact hpow
  have hc2lox : IsLoxodromic (c * c) x :=
    isLoxodromic_of_commute_of_orbitNearAxis hiso hacy hnear hgn hcomm hc2fin
  obtain ⟨p, r, hp, hr, hpow⟩ :=
    exists_common_zpow_of_commute_of_orbitNearAxis hiso hacy hnear hgn hc2lox
      hcomm
  have hsq : c ^ (2 : ℤ) = c * c := by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast, pow_two]
  refine ⟨n * r, 2 * p, mul_ne_zero hn hr,
    mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) hp, ?_⟩
  calc g ^ (n * r) = (g ^ n) ^ r := by rw [zpow_mul]
    _ = (c * c) ^ p := hpow.symm
    _ = (c ^ (2 : ℤ)) ^ p := by rw [hsq]
    _ = c ^ (2 * p) := by rw [← zpow_mul]

/-- The same over a torsion-free ambient group. -/
theorem exists_common_zpow_of_mem_elementaryClosure_of_axis'
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x)
    (htf : IsPowerTorsionFree G) {g c : G} (hg : IsLoxodromic g x)
    (hc : c ∈ elementaryClosure g) (hc1 : c ≠ 1) :
    ∃ i m : ℤ, i ≠ 0 ∧ m ≠ 0 ∧ g ^ i = c ^ m :=
  exists_common_zpow_of_mem_elementaryClosure_of_infiniteOrder' hiso hacy hnear
    hg hc (htf.not_isOfFinOrder hc1)

/-- Two independent elementary closures share no infinite subgroup, over a
torsion-free ambient group, without the dichotomy. -/
theorem not_infinite_le_inf_elementaryClosure_of_torsionFree'
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x)
    (htf : IsPowerTorsionFree G) {g k : G} (hg : IsLoxodromic g x)
    (hk : IsLoxodromic k x) (hind : Independent g k x) {K : Subgroup G}
    (hKg : K ≤ elementaryClosure g) (hKk : K ≤ elementaryClosure k)
    (hKinf : ((K : Subgroup G) : Set G).Infinite) : False := by
  obtain ⟨c, hcK, hc1⟩ : ∃ c : G, c ∈ K ∧ c ≠ 1 := by
    by_contra hnone
    push Not at hnone
    refine hKinf (Set.Finite.subset (Set.finite_singleton (1 : G)) ?_)
    intro y hy
    rw [Set.mem_singleton_iff]
    exact hnone y hy
  obtain ⟨i₁, m₁, hi₁, hm₁, he₁⟩ :=
    exists_common_zpow_of_mem_elementaryClosure_of_axis' hiso hacy hnear htf
      hg (hKg hcK) hc1
  obtain ⟨i₂, m₂, hi₂, hm₂, he₂⟩ :=
    exists_common_zpow_of_mem_elementaryClosure_of_axis' hiso hacy hnear htf
      hk (hKk hcK) hc1
  have hcommon : g ^ (i₁ * m₂) = k ^ (i₂ * m₁) := by
    calc g ^ (i₁ * m₂) = (g ^ i₁) ^ m₂ := by rw [zpow_mul]
      _ = (c ^ m₁) ^ m₂ := by rw [he₁]
      _ = c ^ (m₁ * m₂) := by rw [← zpow_mul]
      _ = c ^ (m₂ * m₁) := by rw [mul_comm m₁ m₂]
      _ = (c ^ m₂) ^ m₁ := by rw [zpow_mul]
      _ = (k ^ i₂) ^ m₁ := by rw [← he₂]
      _ = k ^ (i₂ * m₁) := by rw [← zpow_mul]
  exact not_independent_of_common_zpow hiso hg (mul_ne_zero hi₁ hm₂)
    (mul_ne_zero hi₂ hm₁) hcommon hind

/-- A loxodromic element inside a normal `s`-normal subgroup, without the
dichotomy. -/
theorem exists_loxodromic_mem_of_isSNormal_of_normal_of_torsionFree' {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {x : X} (hnear : CentralizerOrbitNearAxis G x)
    (hindep : IndependentOfNoCommonZpow G x) (htf : IsPowerTorsionFree G)
    {g : G} (hg : IsLoxodromic g x) {N : Subgroup G} [N.Normal]
    (hN : HullSuitable.IsSNormal N) :
    ∃ q ∈ N, IsLoxodromic q x := by
  have hδ0 : 0 ≤ δ := nonneg_of_isHyperbolicSpace hδ x
  obtain ⟨c, hcN, hc1⟩ := exists_ne_one_mem_of_isSNormal hN
  have hcfin : ¬ IsOfFinOrder c := htf.not_isOfFinOrder hc1
  rcases independent_conj_inv_or_conj_zpow hiso hindep g c hg with
    hind | ⟨m, n, hm, hn, hpow⟩
  · obtain ⟨K, hmem, hlox⟩ :=
      exists_loxodromic_commutator_of_independent_conjugate hδ hδ0 hiso hcN hg
        hind
    exact ⟨_, hmem, hlox⟩
  · by_cases hmn : m = n
    · rw [hmn] at hpow
      have hcomm : c * g ^ n = g ^ n * c := by
        calc c * g ^ n = c * g ^ n * c⁻¹ * c := by group
          _ = g ^ n * c := by rw [hpow]
      have hgn : IsLoxodromic (g ^ n) x := isLoxodromic_zpow hiso hg hn
      exact ⟨c, hcN,
        isLoxodromic_of_commute_of_orbitNearAxis hiso hacy hnear hgn hcomm hcfin⟩
    · exact exists_loxodromic_mem_of_conj_zpow_eq_zpow_of_ne hiso hcN hg hmn hpow

/-- Steps three and four of Osin's Lemma 7.1, without the dichotomy. -/
theorem actsNonElementarily_of_mem_of_isSNormal_of_torsionFree'
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x)
    (hindep : IndependentOfNoCommonZpow G x) (htf : IsPowerTorsionFree G)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) {N : Subgroup G}
    (hN : HullSuitable.IsSNormal N) {g : G} (hgN : g ∈ N)
    (hg : IsLoxodromic g x) : ActsNonElementarily N x := by
  have hcen : NoIndependentPairInCentralizer G x :=
    noIndependentPairInCentralizer_of_orbitNearAxis hiso hacy hnear
  obtain ⟨h, hhN, hh⟩ : ∃ h : G, h ∈ N ∧ h ∉ elementaryClosure g := by
    by_contra hcon
    push Not at hcon
    have hNle : N ≤ elementaryClosure g := by
      intro y hy
      exact hcon y hy
    obtain ⟨f, hf⟩ :=
      exists_notMem_elementaryClosure_of_centralizer hiso hcen hG hg
    have hkl : IsLoxodromic (f * g * f⁻¹) x := isLoxodromic_conj hiso hg
    have hindgk : Independent g (f * g * f⁻¹) x := by
      refine hindep g (f * g * f⁻¹) hg hkl ?_
      intro p r hp hr heq
      exact hf (mem_elementaryClosure_of_common_zpow_conj hp hr heq)
    have hTg : twistedIntersection N f⁻¹ ≤ elementaryClosure g := by
      intro y hy
      exact hNle (mem_twistedIntersection.mp hy).1
    have hTk : twistedIntersection N f⁻¹ ≤ elementaryClosure (f * g * f⁻¹) := by
      intro y hy
      refine mem_elementaryClosure_conj' (a := f) ?_
      have h2 := (mem_twistedIntersection.mp hy).2
      rw [inv_inv] at h2
      exact hNle h2
    exact not_infinite_le_inf_elementaryClosure_of_torsionFree' hiso hacy hnear
      htf hg hkl hindgk hTg hTk (infinite_twistedIntersection hN f⁻¹)
  exact actsNonElementarily_of_notMem_elementaryClosure hiso hindep hgN hhN hg hh

/-- **Osin's Lemma 7.1 for a normal `s`-normal subgroup over a torsion-free
ambient group**, with two residuals: `CentralizerOrbitNearAxis` and
`IndependentOfNoCommonZpow`. -/
theorem actsNonElementarily_of_isSNormal_of_normal_of_torsionFree' {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hiso : IsIsometricAction G X)
    (hacy : IsAcylindrical G X) {x : X}
    (hnear : CentralizerOrbitNearAxis G x)
    (hindep : IndependentOfNoCommonZpow G x) (htf : IsPowerTorsionFree G)
    (hG : ActsNonElementarily (⊤ : Subgroup G) x) {N : Subgroup G} [N.Normal]
    (hN : HullSuitable.IsSNormal N) : ActsNonElementarily N x := by
  obtain ⟨g₁, -, -, -, hg₁, -, -⟩ := id hG
  obtain ⟨g, hgN, hg⟩ :=
    exists_loxodromic_mem_of_isSNormal_of_normal_of_torsionFree' hδ hiso hacy
      hnear hindep htf hg₁ hN
  exact actsNonElementarily_of_mem_of_isSNormal_of_torsionFree' hiso hacy hnear
    hindep htf hG hN hgN hg

/-! ## At Hull's Cayley graph, with both residuals discharged -/

section Cayley

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Osin's Lemma 7.1, closed**, in the case `lem:saturation` uses. -/
theorem osinNonElementary_of_torsionFree_normal_closed {G : Type u} [Group G]
    (A : HullGeneratingSet G) (htf : IsPowerTorsionFree G) (N : Subgroup G)
    [N.Normal] (hN : HullSuitable.IsSNormal N) :
    ActsNonElementarily N (Cayley.base A.alphabet) :=
  actsNonElementarily_of_isSNormal_of_normal_of_torsionFree' A.hyperbolic
    A.isometric A.acylindrical (ElementaryMorse.centralizerOrbitNearAxis_cayley A)
    (ElementaryMorse.independentOfNoCommonZpow_cayley A) htf A.nonElementary hN

/-- The manuscript theorem `TheoremCAssembly.osinLemma71`. -/
theorem osinLemma71_closed :
    ∀ {G : Type} [Group G] (A : HullGeneratingSet G),
      IsPowerTorsionFree G → ∀ (N : Subgroup G) [N.Normal],
        HullSuitable.IsSNormal N →
          ActsNonElementarily N (Cayley.base A.alphabet) :=
  fun A htf N _ hN => osinNonElementary_of_torsionFree_normal_closed A htf N hN

end Cayley

end Elementary
end GGT
end GroupApproximation
