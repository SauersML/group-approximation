import GroupApproximation.GGT.HullSCLemma49StablePowerChain
import GroupApproximation.GGT.HullSCLemma49ScaledPrimePiece

/-!
# The short loxodromic branch of Hull's Lemma 4.9

Hull's auxiliary assertion `aaqg` uses Bowditch Lemma 2.2 to obtain a
uniform positive lower bound for stable translation lengths in an
acylindrical hyperbolic Cayley graph.  For periods of length at most
`8 * delta + 1`, an Archimedean choice then gives one multiplicative
quasi-geodesic constant for every power boundary.

This module combines that power-chain estimate with the shared relative
Greendlinger certificate and the scaled prime-piece contradiction.  Its
geometric input is exactly Bowditch's uniform translation gap; the proof of
that gap from acylindricity is separated into the following Bowditch module.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-! ## Bowditch's uniform stable-translation conclusion -/

/-- Bowditch Lemma 2.2 specialized to a Cayley action: all loxodromic
elements have stable translation length bounded below by one positive
constant depending only on the action. -/
def CayleyUniformLoxodromicTranslationGap
    {G : Type u} [Group G] (A : Alphabet G) : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ g : G,
    IsLoxodromic g (Cayley.base A) →
      d ≤ stableTranslation g (Cayley.base A)

/-- The Bowditch conclusion holds in the one-point model because that action
has no loxodromic element. -/
theorem cayleyUniformLoxodromicTranslationGap_trivialModel
    (A : Alphabet PUnit) :
    CayleyUniformLoxodromicTranslationGap A := by
  refine ⟨1, by norm_num, ?_⟩
  intro g hlox
  have hpos : 0 < stableTranslation g (Cayley.base A) :=
    stableTranslation_pos_of_isLoxodromic
      (isIsometricAction_cayley A) hlox
  have hupper := stableTranslation_le_dist_smul g (Cayley.base A)
  have hg : g = 1 := Subsingleton.elim _ _
  rw [hg, one_smul, dist_self] at hupper
  linarith

/-! ## Archimedean and scale choices -/

/-- A positive real lower bound and a finite period bound determine a
positive natural multiplicative constant for the stable-translation power
chain. -/
theorem exists_lemma49StablePowerConstant
    {d : ℝ} (hd : 0 < d) (L : ℕ) :
    ∃ M : ℕ, 0 < M ∧ (L : ℝ) ≤ d * M := by
  obtain ⟨M, hM⟩ := exists_nat_gt ((L : ℝ) / d)
  have hquotientNonneg : (0 : ℝ) ≤ (L : ℝ) / d := by positivity
  have hMReal : (0 : ℝ) < (M : ℝ) :=
    lt_of_le_of_lt hquotientNonneg hM
  have hLM' : (L : ℝ) ≤ (M : ℝ) * d :=
    (div_le_iff₀ hd).mp hM.le
  refine ⟨M, ?_, ?_⟩
  · exact_mod_cast hMReal
  · simpa only [mul_comm] using hLM'

/-- The divisor used for two repeated blocks satisfies all three numerical
conditions in the scaled shadow argument. -/
theorem lemma49_scaledDivisor_bounds (M : ℕ) (hM : 0 < M) :
    0 < 100 * (M + 1) ∧
      6 ≤ 100 * (M + 1) ∧
      32 * M ≤ 100 * (M + 1) ∧
      8 ≤ 100 * (M + 1) := by
  omega

/-- The scaled prime-piece coefficient is at most the coefficient used to
select the relative Greendlinger cell. -/
theorem lemma49ScaledFinalMu_le_certificate
    {powerMu divisor : ℕ} (hpowerMu : 0 < powerMu)
    (hdivisor : 0 < divisor) :
    lemma49ScaledFinalMu powerMu divisor ≤ (1 / 1000 : ℝ) := by
  have hpowerMuOne : 1 ≤ powerMu := hpowerMu
  have hdivisorOne : 1 ≤ divisor := hdivisor
  have hfirst : 100000 ≤ 100000 * powerMu := by
    simpa only [mul_one] using Nat.mul_le_mul_left 100000 hpowerMuOne
  have hsecond : 100000 * powerMu ≤
      100000 * powerMu * divisor := by
    simpa only [mul_one] using
      Nat.mul_le_mul_left (100000 * powerMu) hdivisorOne
  have hdenNat : 1000 ≤ 100000 * powerMu * divisor := by
    exact le_trans (by norm_num) (le_trans hfirst hsecond)
  have hdenReal : (1000 : ℝ) ≤
      (100000 * powerMu * divisor : ℕ) := by
    exact_mod_cast hdenNat
  have hthousand : (0 : ℝ) < 1000 := by norm_num
  have hdenPos : (0 : ℝ) < (100000 * powerMu * divisor : ℕ) :=
    lt_of_lt_of_le hthousand hdenReal
  dsimp [lemma49ScaledFinalMu]
  exact one_div_le_one_div_of_le hthousand hdenReal

/-! ## Scale domination -/

/-- The single short-loxodromic relator scale contains the shortening scale
and the connector scale used by the scaled prime-piece contradiction. -/
theorem lemma49_shortLox_scales
    {eps divisor target scale : ℕ} (hdivisor : 0 < divisor)
    (hscale : scale = 1000 * divisor * (target + 2 * eps + 2)) :
    100 * (2 * eps + 1) ≤ scale ∧
      1000 * (2 * eps + 2) ≤ scale := by
  subst scale
  have hdivisorOne : 1 ≤ divisor := hdivisor
  have hfactor : 2 * eps + 2 ≤ target + 2 * eps + 2 := by omega
  have hbase : 1000 * (2 * eps + 2) ≤
      1000 * (target + 2 * eps + 2) :=
    Nat.mul_le_mul_left 1000 hfactor
  have hdivided : 1000 * (target + 2 * eps + 2) ≤
      1000 * divisor * (target + 2 * eps + 2) := by
    calc
      1000 * (target + 2 * eps + 2) =
          (1000 * 1) * (target + 2 * eps + 2) := by ring
      _ ≤ (1000 * divisor) * (target + 2 * eps + 2) :=
        Nat.mul_le_mul_right (target + 2 * eps + 2)
          (Nat.mul_le_mul_left 1000 hdivisorOne)
      _ = 1000 * divisor * (target + 2 * eps + 2) := rfl
  have hrelator : 1000 * (2 * eps + 2) ≤
      1000 * divisor * (target + 2 * eps + 2) :=
    le_trans hbase hdivided
  constructor
  · exact le_trans (by omega) hrelator
  · exact hrelator

/-! ## Model checks for the numerical choices -/

/-- Concrete constants satisfy the stable-power parameter conclusion. -/
theorem lemma49StablePowerConstant_model :
    ∃ M : ℕ, 0 < M ∧ (9 : ℝ) ≤ (1 / 2 : ℝ) * M := by
  exact exists_lemma49StablePowerConstant (by norm_num) 9

end HullSC
end GroupApproximation
