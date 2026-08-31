import GroupApproximation.GGT.ElementaryCoarseTranslationProperAction
import GroupApproximation.GGT.ElementaryMorseBiInfinite

/-!
# Quasiconvexity of an elementary-closure orbit

The uniform orbit-closeness conclusion of DGO Lemma 6.5 supplies condition (b)
in DGO Theorem 4.42: every point of the `E(h)`-orbit lies within one uniform
distance of the power orbit of `h`.  The geodesic-space proof below obtains
that bound directly from long periodic windows and the middle-chain Morse
lemma.  A second route accepts the stronger coarse-translation statement as an
input.  Once orbit closeness is known, appending the elementary-orbit endpoint
to a finite power-orbit chain proves quasiconvexity without requiring the whole
ambient space to be geodesic.
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

/-- **The elementary-closure orbit lies uniformly near the power orbit.**

This is the finite-window form of the quasi-axis argument in DGO Lemma 6.5.
For `a ∈ E(h)`, choose a positive `n` for which conjugation by `a` sends
`hⁿ` to `hⁿ` or `h⁻ⁿ`.  On an arbitrarily long window whose radius is a
multiple of `n`, compare the `h`-orbit chain translated by `a` with the
untranslated `h`-chain.  In the reversing case compare it with the
`h⁻¹`-chain instead.  The endpoint errors are both `d(a x, x)`, while the
middle-chain Morse bound is independent of that error. -/
theorem elementaryClosureOrbitClose_of_geodesic
    {δ : ℝ} (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ)
    (hgeo : IsGeodesicSpace X) (hiso : IsIsometricAction G X)
    {h : G} {x : X} (hlox : IsLoxodromic h x) :
    ElementaryClosureOrbitClose h x := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hlox
  obtain ⟨K, R, hK, _hR, hmiddle⟩ :=
    ElementaryMorse.exists_bound_middle_chain_near_chain
      (D := dist x (h • x)) hδ hδ0 dist_nonneg hl hB hgeo
  refine ⟨K, hK, ?_⟩
  intro a ha
  obtain ⟨n, hn, hpos | hneg⟩ :=
    exists_conj_positive_zpow_eq_or_of_mem_elementaryClosure hiso hlox ha
  all_goals
    let E : ℝ := dist (a • x) x
    have hE : 0 ≤ E := dist_nonneg
    obtain ⟨Q, hQ⟩ := exists_nat_gt ((E + R + B) / l)
    have hQlarge : E + R + B < l * (Q : ℝ) := by
      rw [div_lt_iff₀ hl] at hQ
      simpa only [mul_comm] using hQ
    let P : ℕ := n * Q
    let N : ℕ := P + P
    have hQPnat : Q ≤ P := by
      dsimp [P]
      exact Nat.le_mul_of_pos_left Q hn
    have hQP : (Q : ℝ) ≤ (P : ℝ) := by exact_mod_cast hQPnat
    have hfar : E + R + B ≤ l * (P : ℝ) :=
      (le_of_lt hQlarge).trans
        (mul_le_mul_of_nonneg_left hQP (le_of_lt hl))
    have hPN : P ≤ N := by dsimp [N]; omega
    have hNP : N - P = P := by dsimp [N]; omega
    have hPcast : (P : ℤ) = (n : ℤ) * (Q : ℤ) := by
      simp [P]
    have hswap_of_conj : ∀ {q r : G}, a * q * a⁻¹ = r → a * q = r * a := by
      intro q r hconj
      calc
        a * q = (a * q * a⁻¹) * a := by group
        _ = r * a := by rw [hconj]
    have hdist_of_swap : ∀ {q r : G}, a * q = r * a →
        dist (a • (q • x)) (r • x) = E := by
      intro q r hswap
      calc
        dist (a • (q • x)) (r • x) =
            dist (r • (a • x)) (r • x) := by
              rw [← mul_smul, hswap, mul_smul]
        _ = dist (a • x) x := hiso r (a • x) x
        _ = E := rfl
  · have hPpos : a * h ^ (P : ℤ) * a⁻¹ = h ^ (P : ℤ) := by
      calc
        a * h ^ (P : ℤ) * a⁻¹ =
            a * (h ^ (n : ℤ)) ^ (Q : ℤ) * a⁻¹ := by
              rw [hPcast, zpow_mul]
        _ = (a * h ^ (n : ℤ) * a⁻¹) ^ (Q : ℤ) :=
          conj_zpow_eq a (h ^ (n : ℤ)) (Q : ℤ)
        _ = (h ^ (n : ℤ)) ^ (Q : ℤ) := by rw [hpos]
        _ = h ^ ((n : ℤ) * (Q : ℤ)) := by rw [← zpow_mul]
        _ = h ^ (P : ℤ) := by rw [← hPcast]
    have hPneg : a * h ^ (-(P : ℤ)) * a⁻¹ = h ^ (-(P : ℤ)) := by
      calc
        a * h ^ (-(P : ℤ)) * a⁻¹ =
            (a * h ^ (P : ℤ) * a⁻¹)⁻¹ := by group
        _ = (h ^ (P : ℤ))⁻¹ := by rw [hPpos]
        _ = h ^ (-(P : ℤ)) := by group
    let y : ℕ → X := ElementaryMorse.orbitChain h x P
    let z : ℕ → X := fun i => a • ElementaryMorse.orbitChain h x P i
    have hyEdge : ∀ i, i < N →
        dist (y i) (y (i + 1)) ≤ dist x (h • x) := by
      intro i _
      exact le_of_eq (ElementaryMorse.orbitChain_edge hiso h x P i)
    have hyProg : ∀ i j, i ≤ j → j ≤ N →
        l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j) := by
      intro i j hij _
      exact ElementaryMorse.orbitChain_prog hiso hlin P hij
    have hzEdge : ∀ i, i < N →
        dist (z i) (z (i + 1)) ≤ dist x (h • x) := by
      intro i _
      dsimp [z]
      rw [hiso]
      exact le_of_eq (ElementaryMorse.orbitChain_edge hiso h x P i)
    have hzProg : ∀ i j, i ≤ j → j ≤ N →
        l * ((j - i : ℕ) : ℝ) - B ≤ dist (z i) (z j) := by
      intro i j hij _
      dsimp [z]
      rw [hiso]
      exact ElementaryMorse.orbitChain_prog hiso hlin P hij
    have hy0 : y 0 = (h ^ (-(P : ℤ))) • x := by
      simp [y, ElementaryMorse.orbitChain]
    have hyN : y N = (h ^ (P : ℤ)) • x := by
      unfold y ElementaryMorse.orbitChain
      have hindex : ((N : ℤ) - (P : ℤ)) = (P : ℤ) := by
        dsimp [N]
        push_cast
        ring
      rw [hindex]
    have hz0 : z 0 = a • ((h ^ (-(P : ℤ))) • x) := by
      simp [z, ElementaryMorse.orbitChain]
    have hzN : z N = a • ((h ^ (P : ℤ)) • x) := by
      unfold z ElementaryMorse.orbitChain
      have hindex : ((N : ℤ) - (P : ℤ)) = (P : ℤ) := by
        dsimp [N]
        push_cast
        ring
      rw [hindex]
    have hclose0 : dist (z 0) (y 0) ≤ E := by
      rw [hz0, hy0]
      exact le_of_eq (hdist_of_swap (hswap_of_conj hPneg))
    have hcloseN : dist (z N) (y N) ≤ E := by
      rw [hzN, hyN]
      exact le_of_eq (hdist_of_swap (hswap_of_conj hPpos))
    obtain ⟨i, _hiN, hnear⟩ := hmiddle E hE y z N
      hyEdge hyProg hzEdge hzProg hclose0 hcloseN P hPN hfar (by rwa [hNP])
    refine ⟨(i : ℤ) - (P : ℤ), ?_⟩
    have hzP : z P = a • x := by
      simp [z, ElementaryMorse.orbitChain]
    have hyi : y i = (h ^ ((i : ℤ) - (P : ℤ))) • x := rfl
    rw [hzP, hyi] at hnear
    rwa [dist_comm] at hnear
  · have hPneg : a * h ^ (P : ℤ) * a⁻¹ = h ^ (-(P : ℤ)) := by
      calc
        a * h ^ (P : ℤ) * a⁻¹ =
            a * (h ^ (n : ℤ)) ^ (Q : ℤ) * a⁻¹ := by
              rw [hPcast, zpow_mul]
        _ = (a * h ^ (n : ℤ) * a⁻¹) ^ (Q : ℤ) :=
          conj_zpow_eq a (h ^ (n : ℤ)) (Q : ℤ)
        _ = (h ^ (-(n : ℤ))) ^ (Q : ℤ) := by rw [hneg]
        _ = h ^ (-(P : ℤ)) := by
          rw [← zpow_mul]
          congr 1
          rw [hPcast]
          ring
    have hnegP : a * h ^ (-(P : ℤ)) * a⁻¹ = h ^ (P : ℤ) := by
      calc
        a * h ^ (-(P : ℤ)) * a⁻¹ =
            (a * h ^ (P : ℤ) * a⁻¹)⁻¹ := by group
        _ = (h ^ (-(P : ℤ)))⁻¹ := by rw [hPneg]
        _ = h ^ (P : ℤ) := by group
    have hDinv : dist x (h⁻¹ • x) = dist x (h • x) := by
      simpa only [zpow_neg, zpow_one] using
        (dist_zpow_neg (g := h) (x := x) hiso (1 : ℤ))
    have hlinInv : ∀ m : ℕ,
        l * (m : ℝ) - B ≤ dist x (((h⁻¹) ^ m) • x) := by
      intro m
      have hm : dist x (((h⁻¹) ^ m) • x) = dist x ((h ^ m) • x) := by
        simpa only [zpow_neg, zpow_natCast, inv_pow] using
          (dist_zpow_neg (g := h) (x := x) hiso (m : ℤ))
      rw [hm]
      exact hlin m
    let y : ℕ → X := ElementaryMorse.orbitChain h⁻¹ x P
    let z : ℕ → X := fun i => a • ElementaryMorse.orbitChain h x P i
    have hyEdge : ∀ i, i < N →
        dist (y i) (y (i + 1)) ≤ dist x (h • x) := by
      intro i _
      rw [← hDinv]
      exact le_of_eq (ElementaryMorse.orbitChain_edge hiso h⁻¹ x P i)
    have hyProg : ∀ i j, i ≤ j → j ≤ N →
        l * ((j - i : ℕ) : ℝ) - B ≤ dist (y i) (y j) := by
      intro i j hij _
      exact ElementaryMorse.orbitChain_prog hiso hlinInv P hij
    have hzEdge : ∀ i, i < N →
        dist (z i) (z (i + 1)) ≤ dist x (h • x) := by
      intro i _
      dsimp [z]
      rw [hiso]
      exact le_of_eq (ElementaryMorse.orbitChain_edge hiso h x P i)
    have hzProg : ∀ i j, i ≤ j → j ≤ N →
        l * ((j - i : ℕ) : ℝ) - B ≤ dist (z i) (z j) := by
      intro i j hij _
      dsimp [z]
      rw [hiso]
      exact ElementaryMorse.orbitChain_prog hiso hlin P hij
    have hy0 : y 0 = (h ^ (P : ℤ)) • x := by
      unfold y ElementaryMorse.orbitChain
      have hzero : ((0 : ℤ) - (P : ℤ)) = -(P : ℤ) := by ring
      rw [hzero, inv_zpow, zpow_neg]
      simp
    have hyN : y N = (h ^ (-(P : ℤ))) • x := by
      unfold y ElementaryMorse.orbitChain
      have hindex : ((N : ℤ) - (P : ℤ)) = (P : ℤ) := by
        dsimp [N]
        push_cast
        ring
      rw [hindex, inv_zpow, ← zpow_neg]
    have hz0 : z 0 = a • ((h ^ (-(P : ℤ))) • x) := by
      simp [z, ElementaryMorse.orbitChain]
    have hzN : z N = a • ((h ^ (P : ℤ)) • x) := by
      unfold z ElementaryMorse.orbitChain
      have hindex : ((N : ℤ) - (P : ℤ)) = (P : ℤ) := by
        dsimp [N]
        push_cast
        ring
      rw [hindex]
    have hclose0 : dist (z 0) (y 0) ≤ E := by
      rw [hz0, hy0]
      exact le_of_eq (hdist_of_swap (hswap_of_conj hnegP))
    have hcloseN : dist (z N) (y N) ≤ E := by
      rw [hzN, hyN]
      exact le_of_eq (hdist_of_swap (hswap_of_conj hPneg))
    obtain ⟨i, _hiN, hnear⟩ := hmiddle E hE y z N
      hyEdge hyProg hzEdge hzProg hclose0 hcloseN P hPN hfar (by rwa [hNP])
    refine ⟨-((i : ℤ) - (P : ℤ)), ?_⟩
    have hzP : z P = a • x := by
      simp [z, ElementaryMorse.orbitChain]
    have hyi : y i = (h ^ (-((i : ℤ) - (P : ℤ)))) • x := by
      unfold y ElementaryMorse.orbitChain
      rw [inv_zpow, ← zpow_neg]
    rw [hzP, hyi] at hnear
    rwa [dist_comm] at hnear

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
