import GroupApproximation.GGT.HullSCLemma49LongPeriod
import GroupApproximation.GGT.HullSCLemma49ShortLoxodromic

/-!
# Fixed-hyperbolicity-constant forms of Hull's Lemma 4.9 branches

The long and short loxodromic branches must use the same four-point constant
so their period bounds are complementary.  This module exposes both parameter
constructions with a caller-supplied constant.  The long branch uses the fixed
prime-piece scale, while the short branch uses Bowditch's stable-translation
gap and the scaled prime-piece estimate.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-- The long-period contradiction with a caller-supplied four-point
hyperbolicity constant. -/
theorem exists_parameters_false_of_longPeriod_powerDiagram_fixedDelta
    (hgeom : RelativeGreendlingerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (hrot : ∀ {eps : ℕ} {boundaryWord' : List G}
      {relator' : List (GGT.RelLetter G Lambda)}
      (C : RelativeBoundaryContiguity D eps boundaryWord' relator'),
      C.rotation = 0)
    {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) :
    ∃ (eps rho : ℕ),
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        (v : List (GGT.RelLetter G Lambda)), v ∈ W →
        RelWord.IsLemma49Input D W eps (1 / 100000) rho →
          ∀ (g : G) (n : ℕ),
            IsShortestModuloConjugacy D.alphabet.carrier
              (Subgroup.normalClosure
                ({GGT.RelLetter.listVal v} : Set G)) g →
            ∀ Z : Lemma49GeodesicPowerDiagram D v g n,
              8 * delta + 2 ≤ Z.boundaryWord.length → False := by
  have hmuCertPos : (0 : ℝ) < 1 / 1000 := by norm_num
  have hmuCertUpper : (1 / 1000 : ℝ) ≤ 1 / 16 := by norm_num
  obtain ⟨epsCert, rho₀, hcertificate⟩ :=
    exists_lemma49RelativeGreendlingerCell_of_relativeGreendlinger
      hgeom D hemb (1 / 1000) hmuCertPos hmuCertUpper hrot
  obtain ⟨K, hshadow⟩ :=
    exists_lemma49ContiguityShadow_constant delta epsCert
  let b := 8 * delta + 2
  let eps := max epsCert (2 * K)
  let scale := 1000 * (4 * b + 24 * K + 18 * epsCert + 18)
  let rho := max rho₀ scale
  have hepsCert : epsCert ≤ eps := Nat.le_max_left _ _
  have hconnectors : 2 * K ≤ eps := Nat.le_max_right _ _
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : scale ≤ rho := Nat.le_max_right _ _
  refine ⟨eps, rho, ?_⟩
  intro W v hv hinput g n hshort Z hlongPeriod
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  letI : N.Normal := Subgroup.normalClosure_normal
  have hfinalSym : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 100000) rho := hinput.restrict_symmetrized hv
  have hmuMono : (1 / 100000 : ℝ) ≤ 1 / 1000 := by norm_num
  have hcertInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsCert (1 / 1000) rho :=
    hfinalSym.mono_parameters hepsCert hmuMono le_rfl
  obtain ⟨C⟩ := hcertificate rho hrho₀ v g n hcertInput Z
  obtain ⟨Sh⟩ := hshadow G inferInstance Lambda D v g n rho Z C N
    inferInstance hdelta hcertInput hshort hlongPeriod
  apply false_of_longPeriod_powerDiagram_of_cell D Z C Sh hdelta hshort
    hcertInput hfinalSym
  · simpa only [b, scale] using hrhoScale
  · exact hconnectors
  · exact hlongPeriod

/-- The short-loxodromic contradiction with the same caller-supplied
four-point hyperbolicity constant. -/
theorem exists_parameters_false_of_shortLoxodromic_powerDiagram_fixedDelta
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
  let target : ℕ := 2 * lemma49PowerShadowError M b K epsCert + 2
  let scale : ℕ := 1000 * divisor * (target + 2 * epsCert + 2)
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
  have hLOne : 1 ≤ L := hLPos
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

end HullSC
end GroupApproximation
