import GroupApproximation.GGT.HullSCLemma49ShortLoxodromic
import GroupApproximation.GGT.ElementaryBowditchProof
import GroupApproximation.GGT.CayleyGeodesicQuotient

/-!
# Bowditch's uniform translation gap for Hull's Lemma 4.9

Bowditch Lemma 2.2 states that an acylindrical action on a hyperbolic graph
has a uniform positive lower bound on stable lengths of its loxodromic
elements.  The proof here uses the midpoint and acylindricity count already
proved for Bowditch's elliptic/loxodromic dichotomy.

If the stable translation of a loxodromic element were below a fixed small
slope, convergence of normalized displacements would give a global affine
upper bound with that slope.  The finite-window count then produces more
powers than acylindricity permits.  The result is proved first in a geodesic
hyperbolic space and then pulled back from the metric realization of a Cayley
graph.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.GGT

universe u v

/-! ## An affine bound above the stable translation -/

/-- Every slope strictly above stable translation gives a global affine upper
bound for the displacement sequence.  This is the quantitative variant of
the zero-translation estimate in the proof of Bowditch's dichotomy. -/
theorem exists_affine_dist_bound_of_stableTranslation_lt
    {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] (hiso : IsIsometricAction G X)
    {c : G} {x : X} {eta : ℝ}
    (hstable : stableTranslation c x < eta) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ n : ℕ, dist x ((c ^ n) • x) ≤ M + eta * n := by
  have htend := tendsto_stableTranslation hiso c x
  have heventually := htend.eventually_lt_const hstable
  rw [Filter.eventually_atTop] at heventually
  obtain ⟨J, hJ⟩ := heventually
  refine ⟨(J : ℝ) * dist x (c • x),
    mul_nonneg (Nat.cast_nonneg J) dist_nonneg, ?_⟩
  intro n
  have hM : (0 : ℝ) ≤ (J : ℝ) * dist x (c • x) :=
    mul_nonneg (Nat.cast_nonneg J) dist_nonneg
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · have hzero : dist x ((c ^ (0 : ℕ)) • x) = 0 := by
      rw [pow_zero, one_smul, dist_self]
    rw [hzero]
    simp only [Nat.cast_zero, mul_zero]
    simpa only [add_zero] using hM
  · by_cases hnJ : J ≤ n
    · have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
      have hratio : dist x ((c ^ n) • x) / (n : ℝ) < eta := hJ n hnJ
      rw [div_lt_iff₀ hnReal] at hratio
      linarith
    · push Not at hnJ
      have hlinear := dist_pow_le hiso c x n
      have hnJReal : (n : ℝ) ≤ (J : ℝ) := by exact_mod_cast hnJ.le
      have hmono : (n : ℝ) * dist x (c • x) ≤
          (J : ℝ) * dist x (c • x) :=
        mul_le_mul_of_nonneg_right hnJReal dist_nonneg
      have hetaNonneg : 0 ≤ eta :=
        le_trans (stableTranslation_nonneg c x) hstable.le
      have hetaN : 0 ≤ eta * (n : ℝ) :=
        mul_nonneg hetaNonneg (Nat.cast_nonneg n)
      linarith

/-! ## The uniform gap in a geodesic hyperbolic space -/

/-- Bowditch Lemma 2.2 in a geodesic hyperbolic space.  Acylindricity at
radius `8 * delta + 1` fixes a cardinal bound `N`; the slope
`1 / (4 * (N + 1))` cannot be an upper bound for the stable translation of a
loxodromic element, because the midpoint count would produce more than `N`
small movers of two far-apart points. -/
theorem exists_uniform_stableTranslation_lower_of_geodesic
    {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
    [MulAction G X] {delta : ℝ}
    (hdelta : IsHyperbolicSpace delta X) (hdeltaNonneg : 0 ≤ delta)
    (hgeodesic : IsGeodesicSpace X) (hisometric : IsIsometricAction G X)
    (hacylindrical : IsAcylindrical G X) (x : X) :
    ∃ d : ℝ, 0 < d ∧ ∀ c : G, IsLoxodromic c x →
      d ≤ stableTranslation c x := by
  obtain ⟨R, N, hRN⟩ :=
    hacylindrical (8 * delta + 1) (by linarith)
  let d : ℝ := (4 * ((N : ℝ) + 1))⁻¹
  have hdenominator : (0 : ℝ) < 4 * ((N : ℝ) + 1) := by positivity
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdN : 4 * d * ((N : ℝ) + 1) ≤ 1 := by
    have heq : 4 * d * ((N : ℝ) + 1) =
        (4 * ((N : ℝ) + 1)) * (4 * ((N : ℝ) + 1))⁻¹ := by
      dsimp [d]
      ring
    rw [heq, mul_inv_cancel₀ (ne_of_gt hdenominator)]
  refine ⟨d, hd, ?_⟩
  intro c hlox
  by_contra hnotLower
  have hstable : stableTranslation c x < d := lt_of_not_ge hnotLower
  obtain ⟨M, hMNonneg, hMbound⟩ :=
    exists_affine_dist_bound_of_stableTranslation_lt hisometric hstable
  obtain ⟨V, hV⟩ :=
    exists_nat_gt (2 * (2 * M + 1) * ((N : ℝ) + 1))
  let S : ℝ := M + d * (V : ℝ)
  have hVNonneg : (0 : ℝ) ≤ (V : ℝ) := Nat.cast_nonneg V
  have hSNonneg : (0 : ℝ) ≤ S := by
    dsimp [S]
    exact add_nonneg hMNonneg (mul_nonneg hd.le hVNonneg)
  let K : ℕ := Nat.floor (2 * S) + 1
  have hKgt : 2 * S < (K : ℝ) := by
    dsimp [K]
    push_cast
    exact Nat.lt_floor_add_one (2 * S)
  have hKle : (K : ℝ) ≤ 2 * S + 1 := by
    dsimp [K]
    push_cast
    have hfloor := Nat.floor_le (by linarith : (0 : ℝ) ≤ 2 * S)
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hKV : K * (N + 1) < V := by
    have hstep : 2 * d * ((N : ℝ) + 1) * (V : ℝ) ≤ (V : ℝ) / 2 := by
      have hmul := mul_le_mul_of_nonneg_right hdN hVNonneg
      linarith
    have hproduct : (2 * S + 1) * ((N : ℝ) + 1) =
        (2 * M + 1) * ((N : ℝ) + 1) +
          2 * d * ((N : ℝ) + 1) * (V : ℝ) := by
      dsimp [S]
      ring
    have hcomparison : (K : ℝ) * ((N : ℝ) + 1) ≤
        (2 * S + 1) * ((N : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hKle hNpos.le
    rw [hproduct] at hcomparison
    have hcast : ((K * (N + 1) : ℕ) : ℝ) < ((V : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast
  have hescape : IsEscaping c x := hlox.isEscaping
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, ∀ n : ℕ, Q ≤ n →
      S + 3 ≤ dist x ((c ^ n) • x) := by
    have heventually := hescape.eventually_ge_atTop (S + 3)
    rw [Filter.eventually_atTop] at heventually
    exact heventually
  have hsmallPower : ∀ i : ℕ, i ≤ V →
      dist x ((c ^ i) • x) ≤ S := by
    intro i hi
    have hbound := hMbound i
    have hmono : d * (i : ℝ) ≤ d * (V : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hd.le
    dsimp [S]
    linarith
  have hwindowUpper : ∀ i : ℕ,
      dist x ((c ^ (Q + i)) • x) ≤
        dist x ((c ^ Q) • x) + dist x ((c ^ i) • x) := by
    intro i
    have hsplit : (c ^ (Q + i)) • x =
        (c ^ Q) • ((c ^ i) • x) := by
      rw [pow_add, mul_smul]
    rw [hsplit]
    refine le_trans
      (dist_triangle x ((c ^ Q) • x) ((c ^ Q) • ((c ^ i) • x))) ?_
    rw [hisometric (c ^ Q) x ((c ^ i) • x)]
  have hwindowLower : ∀ i : ℕ,
      dist x ((c ^ Q) • x) ≤
        dist x ((c ^ (Q + i)) • x) + dist x ((c ^ i) • x) := by
    intro i
    have hswap : dist ((c ^ (Q + i)) • x) ((c ^ Q) • x) =
        dist x ((c ^ i) • x) := by
      have hcalc := hisometric (c ^ Q) ((c ^ i) • x) x
      rw [← mul_smul, ← pow_add] at hcalc
      rw [hcalc]
      exact dist_comm _ _
    calc
      dist x ((c ^ Q) • x) ≤
          dist x ((c ^ (Q + i)) • x) +
            dist ((c ^ (Q + i)) • x) ((c ^ Q) • x) :=
        dist_triangle _ _ _
      _ = dist x ((c ^ (Q + i)) • x) +
          dist x ((c ^ i) • x) := by rw [hswap]
  let box : ℕ → ℕ := fun i =>
    Nat.floor (dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S)
  have hboxNonneg : ∀ i : ℕ, i ≤ V →
      (0 : ℝ) ≤ dist x ((c ^ (Q + i)) • x) -
        dist x ((c ^ Q) • x) + S := by
    intro i hi
    have hlower := hwindowLower i
    have hsmall := hsmallPower i hi
    linarith
  have hboxUpper : ∀ i : ℕ, i ≤ V →
      dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S ≤
        2 * S := by
    intro i hi
    have hupper := hwindowUpper i
    have hsmall := hsmallPower i hi
    linarith
  have hboxRange : ∀ i, i < V → box i < K := by
    intro i hi
    have hiV : i ≤ V := le_of_lt hi
    have hfloor := Nat.floor_le (hboxNonneg i hiV)
    have hupper := hboxUpper i hiV
    have hcast : ((Nat.floor
        (dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S) : ℕ) : ℝ) <
          (K : ℝ) := by
      linarith
    dsimp [box]
    exact_mod_cast hcast
  obtain ⟨y, hy⟩ := GGT.exists_large_fiber box hboxRange hKV
  let F : Finset ℕ :=
    Finset.filter (fun i => box i = y) (Finset.range V)
  have hFcard : N + 1 < F.card := by exact hy
  have hFmem : ∀ i ∈ F, i < V ∧ box i = y := by
    intro i hi
    simpa only [F, Finset.mem_filter, Finset.mem_range] using hi
  have hFne : F.Nonempty := Finset.card_pos.mp (by omega)
  let i₀ : ℕ := F.min' hFne
  have hi₀F : i₀ ∈ F := F.min'_mem hFne
  have hi₀min : ∀ i ∈ F, i₀ ≤ i := by
    intro i hi
    exact F.min'_le i hi
  have hclose : ∀ i ∈ F,
      |dist x ((c ^ (Q + i)) • x) -
        dist x ((c ^ (Q + i₀)) • x)| ≤ 1 := by
    intro i hi
    have hiV : i ≤ V := le_of_lt (hFmem i hi).1
    have hi₀V : i₀ ≤ V := le_of_lt (hFmem i₀ hi₀F).1
    have hfloorEq : Nat.floor
          (dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S) =
        Nat.floor
          (dist x ((c ^ (Q + i₀)) • x) - dist x ((c ^ Q) • x) + S) := by
      change box i = box i₀
      rw [(hFmem i hi).2, (hFmem i₀ hi₀F).2]
    have hA1 := Nat.floor_le (hboxNonneg i hiV)
    have hA2 := Nat.lt_floor_add_one
      (dist x ((c ^ (Q + i)) • x) - dist x ((c ^ Q) • x) + S)
    have hB1 := Nat.floor_le (hboxNonneg i₀ hi₀V)
    have hB2 := Nat.lt_floor_add_one
      (dist x ((c ^ (Q + i₀)) • x) - dist x ((c ^ Q) • x) + S)
    rw [hfloorEq] at hA1 hA2
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨p, hp, hp0, hp1⟩ := hgeodesic x ((c ^ (Q + i₀)) • x)
  have hdistanceNonneg :
      (0 : ℝ) ≤ dist x ((c ^ (Q + i₀)) • x) := dist_nonneg
  have hdistanceLarge :
      S + 3 ≤ dist x ((c ^ (Q + i₀)) • x) :=
    hQ _ (Nat.le_add_right Q i₀)
  have hxmid : dist x (p (dist x ((c ^ (Q + i₀)) • x) / 2)) =
      dist x ((c ^ (Q + i₀)) • x) / 2 := by
    have hsegment := hp 0 ⟨le_rfl, hdistanceNonneg⟩
      (dist x ((c ^ (Q + i₀)) • x) / 2) ⟨by linarith, by linarith⟩
    rw [hp0] at hsegment
    rw [hsegment, abs_of_nonpos (by linarith)]
    ring
  have hmove : ∀ i ∈ F,
      dist (p (dist x ((c ^ (Q + i₀)) • x) / 2))
        ((c ^ (i - i₀)) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) ≤
          8 * delta + 1 := by
    intro i hi
    have hii₀ : i₀ ≤ i := hi₀min i hi
    have hiV : i < V := (hFmem i hi).1
    have hexponent : (i - i₀) + (Q + i₀) = Q + i := by omega
    have hkC : (c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x) =
        (c ^ (Q + i)) • x := by
      rw [← mul_smul, ← pow_add, hexponent]
    have hexponent' : (Q + i₀) + (i - i₀) = Q + i := by omega
    have hsegmentShift :=
      hisometric (c ^ (Q + i₀)) x ((c ^ (i - i₀)) • x)
    rw [← mul_smul, ← pow_add, hexponent'] at hsegmentShift
    have hsmall := hsmallPower (i - i₀) (by omega)
    have hfarWindow : S + 3 ≤ dist x ((c ^ (Q + i)) • x) :=
      hQ _ (Nat.le_add_right Q i)
    have hnearWindow := hclose i hi
    rw [abs_le] at hnearWindow
    obtain ⟨hnearLeft, hnearRight⟩ := hnearWindow
    have hA1 : dist ((c ^ (Q + i₀)) • x)
        ((c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x)) ≤
          dist x ((c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x)) := by
      rw [hkC, hsegmentShift]
      linarith
    have hA2 : dist x ((c ^ (i - i₀)) • x) ≤
        dist x ((c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x)) := by
      rw [hkC]
      linarith
    have hA3 : dist x ((c ^ (Q + i₀)) • x) / 2 ≤
        dist x ((c ^ (i - i₀)) • ((c ^ (Q + i₀)) • x)) := by
      rw [hkC]
      linarith
    have hmain := GGT.dist_smul_midpoint_le hdelta hdeltaNonneg hgeodesic
      hisometric (c ^ (i - i₀)) hp hp0 hp1 hA1 hA2 hA3
    rw [hkC] at hmain
    have habs : |dist x ((c ^ (Q + i₀)) • x) -
        dist x ((c ^ (Q + i)) • x)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℕ,
      dist x ((c ^ (Q + i₀)) • x) + max R 0 ≤
        dist x ((c ^ A) • x) := by
    have heventually := hescape.eventually_ge_atTop
      (dist x ((c ^ (Q + i₀)) • x) + max R 0)
    rw [Filter.eventually_atTop] at heventually
    obtain ⟨A, hAge⟩ := heventually
    exact ⟨A, hAge A le_rfl⟩
  have hfar : R ≤
      dist (p (dist x ((c ^ (Q + i₀)) • x) / 2))
        ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) := by
    have htriangle1 := dist_triangle x
      (p (dist x ((c ^ (Q + i₀)) • x) / 2)) ((c ^ A) • x)
    have htriangle2 := dist_triangle
      (p (dist x ((c ^ (Q + i₀)) • x) / 2))
      ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) ((c ^ A) • x)
    have heq : dist
        ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) ((c ^ A) • x) =
          dist (p (dist x ((c ^ (Q + i₀)) • x) / 2)) x :=
      hisometric (c ^ A) (p (dist x ((c ^ (Q + i₀)) • x) / 2)) x
    have hmidDistance :
        dist (p (dist x ((c ^ (Q + i₀)) • x) / 2)) x =
          dist x ((c ^ (Q + i₀)) • x) / 2 := by
      rw [dist_comm]
      exact hxmid
    have hR : R ≤ max R 0 := le_max_left _ _
    linarith
  obtain ⟨hfinite, hcard⟩ := hRN
    (p (dist x ((c ^ (Q + i₀)) • x) / 2))
    ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) hfar
  have hmaps : ∀ i ∈ (F : Set ℕ), c ^ (i - i₀) ∈
      {g : G |
        dist (p (dist x ((c ^ (Q + i₀)) • x) / 2))
            (g • p (dist x ((c ^ (Q + i₀)) • x) / 2)) ≤ 8 * delta + 1 ∧
        dist ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2))
            (g • ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2))) ≤
              8 * delta + 1} := by
    intro i hi
    have hiF : i ∈ F := Finset.mem_coe.mp hi
    refine ⟨hmove i hiF, ?_⟩
    have hcommute :
        (c ^ (i - i₀)) •
            ((c ^ A) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) =
          (c ^ A) •
            ((c ^ (i - i₀)) • p (dist x ((c ^ (Q + i₀)) • x) / 2)) := by
      simp only [← mul_smul, ← pow_add]
      rw [Nat.add_comm (i - i₀) A]
    rw [hcommute, hisometric (c ^ A)
      (p (dist x ((c ^ (Q + i₀)) • x) / 2))
      ((c ^ (i - i₀)) • p (dist x ((c ^ (Q + i₀)) • x) / 2))]
    exact hmove i hiF
  have hnotFiniteOrder : ¬ IsOfFinOrder c :=
    GGT.not_isOfFinOrder_of_isEscaping hescape
  have hpowerInjective : Function.Injective (fun n : ℕ => c ^ n) := by
    have hzpowInjective : Function.Injective (fun n : ℤ => c ^ n) :=
      injective_zpow_iff_not_isOfFinOrder.mpr hnotFiniteOrder
    intro a b hab
    have hz : c ^ (a : ℤ) = c ^ (b : ℤ) := by
      rw [zpow_natCast, zpow_natCast]
      exact hab
    exact_mod_cast hzpowInjective hz
  have hinjective : Set.InjOn (fun i : ℕ => c ^ (i - i₀)) (F : Set ℕ) := by
    intro i hi j hj hij
    have hi : i₀ ≤ i := hi₀min i (Finset.mem_coe.mp hi)
    have hj : i₀ ≤ j := hi₀min j (Finset.mem_coe.mp hj)
    have hsub : i - i₀ = j - i₀ := hpowerInjective hij
    omega
  have hcount := Set.ncard_le_ncard_of_injOn
    (fun i : ℕ => c ^ (i - i₀)) hmaps hinjective hfinite
  rw [Set.ncard_coe_finset] at hcount
  have hle : F.card ≤ N := le_trans hcount hcard
  omega

/-! ## Transfer to the relative Cayley graph -/

/-- Bowditch's geodesic-space bound pulls back through the metric realization
of a hyperbolic Cayley graph.  The realization changes distances by a bounded
additive amount, so the uniform slope is unchanged; passing from its linear
orbit estimate to stable translation loses only the harmless factor `1/2`.
-/
theorem cayleyUniformLoxodromicTranslationGap_of_hyperbolic_acylindrical
    {G : Type u} [Group G] (A : Alphabet G) {delta : ℝ}
    (hdelta : IsHyperbolicSpace delta (Cayley A))
    (hacylindrical : IsAcylindrical G (Cayley A)) :
    CayleyUniformLoxodromicTranslationGap A := by
  have hdeltaNonneg : 0 ≤ delta :=
    GGT.Elementary.nonneg_of_isHyperbolicSpace hdelta (Cayley.base A)
  let M := CayleyGeodesicModel.modelQuot A hdelta hdeltaNonneg
    (CayleyGeodesicModel.isGeodesicRealisationQuot A)
  have hacylindricalModel : IsAcylindrical G M.W :=
    isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric
      hacylindrical
  obtain ⟨d, hd, huniform⟩ :=
    exists_uniform_stableTranslation_lower_of_geodesic M.hyperbolic
      M.delta_nonneg M.geodesic M.isometric hacylindricalModel
      (M.iota (Cayley.base A))
  refine ⟨d / 2, by positivity, ?_⟩
  intro g hlox
  have hloxModel : IsLoxodromic g (M.iota (Cayley.base A)) :=
    isLoxodromic_map M.distortion_nonneg M.hasAdditiveDistortion
      M.equivariant hlox
  have hstableModel : d ≤
      stableTranslation g (M.iota (Cayley.base A)) :=
    huniform g hloxModel
  have hlinearModel : ∀ n : ℕ,
      d * n ≤ dist (M.iota (Cayley.base A))
        ((g ^ n) • M.iota (Cayley.base A)) := by
    intro n
    have hscaled := mul_le_mul_of_nonneg_right hstableModel
      (Nat.cast_nonneg n)
    exact le_trans hscaled
      (mul_le_dist_pow g (M.iota (Cayley.base A)) n)
  have hlinearCayley : ∀ n : ℕ,
      d * n - M.distortion ≤
        dist (Cayley.base A) ((g ^ n) • Cayley.base A) := by
    intro n
    have hdistortion :=
      M.hasAdditiveDistortion (Cayley.base A) ((g ^ n) • Cayley.base A)
    rw [M.equivariant (g ^ n) (Cayley.base A)] at hdistortion
    have hupper := (abs_le.mp hdistortion).2
    have hlower := hlinearModel n
    linarith
  exact half_le_stableTranslation_of_loxodromic_data
    (B := M.distortion) (isIsometricAction_cayley A) hd hlinearCayley

/-- A hyperbolically embedded relative generating set with acylindrical
Cayley action satisfies the precise Bowditch input used by Hull Lemma 4.9. -/
theorem cayleyUniformLoxodromicTranslationGap_of_hyperbolicallyEmbedded
    {G : Type u} [Group G] {Lambda : Type v}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (hacylindrical : IsAcylindrical G (Cayley D.alphabet)) :
    CayleyUniformLoxodromicTranslationGap D.alphabet := by
  obtain ⟨delta, hdelta⟩ := hemb.hyperbolic
  exact cayleyUniformLoxodromicTranslationGap_of_hyperbolic_acylindrical
    D.alphabet hdelta hacylindrical

/-! ## Model check -/

/-- In the one-point action every positive slope admits the zero affine
bound. -/
theorem affine_dist_bound_trivialModel (eta : ℝ) (heta : 0 < eta) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      dist (PUnit.unit : PUnit) (((1 : PUnit) ^ n) • PUnit.unit) ≤
        M + eta * n := by
  refine ⟨0, le_rfl, ?_⟩
  intro n
  simp only [dist_self, zero_add]
  positivity

end HullSC
end GroupApproximation
