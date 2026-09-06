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

/-! ## The short loxodromic diagram contradiction -/

/-- Bowditch's uniform translation gap and the shared relative Greendlinger
proposition rule out every nontrivial power diagram whose loxodromic period
has length at most `8 * delta + 1`.  This is the short-word case of Hull's
auxiliary assertion `aaqg`, followed by the two-piece argument in Osin
Lemma 6.3 used in Hull Lemma 4.9. -/
theorem exists_parameters_false_of_shortLoxodromic_powerDiagram_at
    (hgeom : RelativeGreendlingerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (hrot : ∀ {eps : ℕ} {boundaryWord' : List G}
      {relator' : List (GGT.RelLetter G Lambda)}
      (C : RelativeBoundaryContiguity D eps boundaryWord' relator'),
      C.rotation = 0)
    {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (hgap : CayleyUniformLoxodromicTranslationGap D.alphabet) :
    ∃ (eps rho : ℕ) (mu : ℝ),
      0 < mu ∧ mu ≤ 1 / 1000 ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        (v : List (GGT.RelLetter G Lambda)), v ∈ W →
        RelWord.IsLemma49Input D W eps mu rho →
          ∀ (g : G) (n : ℕ),
            IsShortestModuloConjugacy D.alphabet.carrier
              (Subgroup.normalClosure
                ({GGT.RelLetter.listVal v} : Set G)) g →
            IsLoxodromic g (Cayley.base D.alphabet) →
            ∀ Z : Lemma49GeodesicPowerDiagram D v g n,
              Z.boundaryWord.length ≤ 8 * delta + 1 → False := by
  obtain ⟨d₀, hd₀, hgapAll⟩ := hgap
  let d : ℝ := min d₀ 1
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hd₀ (by norm_num)
  have hdd₀ : d ≤ d₀ := by
    dsimp [d]
    exact min_le_left _ _
  have hdOne : d ≤ 1 := by
    dsimp [d]
    exact min_le_right _ _
  let L : ℕ := 8 * delta + 1
  have hLPos : 0 < L := by dsimp [L]; omega
  obtain ⟨M, hM, hLM⟩ := exists_lemma49StablePowerConstant hd L
  let b : ℕ := 4 * L
  let divisor : ℕ := 100 * (M + 1)
  have hdivisorBounds := lemma49_scaledDivisor_bounds M hM
  have hdivisorPos : 0 < divisor := by
    simpa only [divisor] using hdivisorBounds.1
  have hdivisorSix : 6 ≤ divisor := by
    simpa only [divisor] using hdivisorBounds.2.1
  have hdivisorMu : 32 * M ≤ divisor := by
    simpa only [divisor] using hdivisorBounds.2.2.1
  have hdivisorEight : 8 ≤ divisor := by
    simpa only [divisor] using hdivisorBounds.2.2.2
  have hmuCertPos : (0 : ℝ) < 1 / 1000 := by norm_num
  have hmuCertUpper : (1 / 1000 : ℝ) ≤ 1 / 16 := by norm_num
  obtain ⟨epsCert, rho₀, hcertificate⟩ :=
    exists_lemma49RelativeGreendlingerCell_of_relativeGreendlinger
      hgeom D hemb (1 / 1000) hmuCertPos hmuCertUpper hrot
  obtain ⟨K, hshadow⟩ :=
    exists_lemma49ContiguityShadow_constant_of_powerChain
      delta epsCert M b hM
  let eps : ℕ := max epsCert (2 * K)
  let target : ℕ :=
    2 * lemma49PowerShadowError M b K epsCert + 2
  let scale : ℕ :=
    1000 * divisor * (target + 2 * epsCert + 2)
  let rho : ℕ := max rho₀ scale
  let mu : ℝ := lemma49ScaledFinalMu M divisor
  have hepsCert : epsCert ≤ eps := Nat.le_max_left _ _
  have hconnectors : 2 * K ≤ eps := Nat.le_max_right _ _
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : scale ≤ rho := Nat.le_max_right _ _
  have hmuPos : 0 < mu := by
    dsimp [mu]
    exact lemma49ScaledFinalMu_pos hM hdivisorPos
  have hmuCert : mu ≤ (1 / 1000 : ℝ) := by
    dsimp [mu]
    exact lemma49ScaledFinalMu_le_certificate hM hdivisorPos
  have hscales :
      100 * (2 * epsCert + 1) ≤ scale ∧
        1000 * (2 * epsCert + 2) ≤ scale := by
    apply lemma49_shortLox_scales hdivisorPos
    rfl
  have hshortScale : 100 * (2 * epsCert + 1) ≤ rho :=
    le_trans hscales.1 hrhoScale
  have hRelatorScale : 1000 * (2 * epsCert + 2) ≤ rho :=
    le_trans hscales.2 hrhoScale
  refine ⟨eps, rho, mu, hmuPos, hmuCert, ?_⟩
  intro W v hv hinput g n hshort hlox Z hshortPeriod
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  letI : N.Normal := Subgroup.normalClosure_normal
  have hfinalSym : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps mu rho := hinput.restrict_symmetrized hv
  have hcertInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsCert (1 / 1000) rho :=
    hfinalSym.mono_parameters hepsCert hmuCert le_rfl
  obtain ⟨C⟩ := hcertificate rho hrho₀ v g n hcertInput Z
  have hlongArc : 4 * Z.boundaryWord.length ≤
      3 * C.boundaryArc.length :=
    four_mul_period_le_three_mul_arc C hcertInput hshortScale hshort
  have hwordNe : Z.boundaryWord ≠ [] := by
    intro hnil
    have hg : g = 1 := by
      have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
        simpa using Z.boundary_geodesic.2.1
      rw [hnil] at hvalue
      calc
        g = GGT.RelLetter.listVal
            ([] : List (GGT.RelLetter G Lambda)) := hvalue.symm
        _ = 1 := GGT.RelLetter.listVal_nil
    exact Z.power_ne_one (by simp [hg])
  have hperiodPos : 0 < Z.boundaryWord.length :=
    List.length_pos_iff.mpr hwordNe
  have harcInfix : C.boundaryArc <:+:
      lemma49BoundaryPower Z.boundaryWord n :=
    ⟨C.boundaryBefore, C.boundaryAfter, C.boundary_decomposition.symm⟩
  obtain ⟨B⟩ := exists_scaledRepeatedBoundaryBlocks_of_lemma49PowerArc
    Z.exponent_pos harcInfix hperiodPos hdivisorSix hlongArc
  have hlength : Z.boundaryWord.length ≤ L := by
    simpa only [L] using hshortPeriod
  have hdStable : d ≤ stableTranslation g (Cayley.base D.alphabet) :=
    le_trans hdd₀ (hgapAll g hlox)
  have hLOne : 1 ≤ L := by exact hLPos
  have hOneL : (1 : ℝ) ≤ (L : ℕ) := by exact_mod_cast hLOne
  have hdL : d ≤ (L : ℕ) := le_trans hdOne hOneL
  have hPowerGlobal := isQuasiGeodesicChainAt_power_of_stableTranslation
    (n := n) D Z.boundary_geodesic hperiodPos hlength hM hd hdStable hdL hLM
  obtain ⟨Sh⟩ := hshadow G inferInstance Lambda D v g n rho Z C hdelta
    hcertInput hPowerGlobal
  have hRel := C.exterior_isQuasiGeodesicChainAt hcertInput
  have hPow := C.powerArc_isQuasiGeodesicChainAt hPowerGlobal
  have hArcScale : divisor * target ≤ C.boundaryArc.length := by
    apply C.boundaryArc_scaled_scale hcertInput hdivisorPos
    simpa only [scale] using hrhoScale
  have hArcScale' : divisor *
      (2 * lemma49PowerShadowError M b K epsCert + 2) ≤
        C.boundaryArc.length := by
    simpa only [target] using hArcScale
  have hfinalInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (lemma49ScaledFinalMu M divisor) rho := by
    simpa only [mu] using hfinalSym
  exact false_of_lemma49ScaledLongArc_contiguityShadow C B Sh hcertInput
    hfinalInput hRel hPow hM hdivisorPos hdivisorMu hdivisorEight
    hArcScale' hRelatorScale hconnectors

/-- The caller-independent form chooses a four-point constant from the
hyperbolically embedded relative Cayley graph. -/
theorem exists_parameters_false_of_shortLoxodromic_powerDiagram
    (hgeom : RelativeGreendlingerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (hrot : ∀ {eps : ℕ} {boundaryWord' : List G}
      {relator' : List (GGT.RelLetter G Lambda)}
      (C : RelativeBoundaryContiguity D eps boundaryWord' relator'),
      C.rotation = 0)
    (hgap : CayleyUniformLoxodromicTranslationGap D.alphabet) :
    ∃ (eps rho delta : ℕ) (mu : ℝ),
      0 < mu ∧ mu ≤ 1 / 1000 ∧
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        (v : List (GGT.RelLetter G Lambda)), v ∈ W →
        RelWord.IsLemma49Input D W eps mu rho →
          ∀ (g : G) (n : ℕ),
            IsShortestModuloConjugacy D.alphabet.carrier
              (Subgroup.normalClosure
                ({GGT.RelLetter.listVal v} : Set G)) g →
            IsLoxodromic g (Cayley.base D.alphabet) →
            ∀ Z : Lemma49GeodesicPowerDiagram D v g n,
              Z.boundaryWord.length ≤ 8 * delta + 1 → False := by
  obtain ⟨delta, hdelta⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  obtain ⟨eps, rho, mu, hmu, hmuUpper, hgood⟩ :=
    exists_parameters_false_of_shortLoxodromic_powerDiagram_at
      hgeom D hemb hrot hdelta hgap
  exact ⟨eps, rho, delta, mu, hmu, hmuUpper, hdelta, hgood⟩

/-! ## Model checks for the numerical choices -/

/-- Concrete constants satisfy the stable-power parameter conclusion. -/
theorem lemma49StablePowerConstant_model :
    ∃ M : ℕ, 0 < M ∧ (9 : ℝ) ≤ (1 / 2 : ℝ) * M := by
  exact exists_lemma49StablePowerConstant (by norm_num) 9

end HullSC
end GroupApproximation
