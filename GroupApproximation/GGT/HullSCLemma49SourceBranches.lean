import GroupApproximation.GGT.HullSCLemma49LongPeriod
import GroupApproximation.GGT.HullSCLemma49Rebase
import GroupApproximation.GGT.HullSCLemma49ShortLoxodromic
import GroupApproximation.GGT.HullSCLemma49SourceGreendlinger
import GroupApproximation.GGT.HullSCLemma49FacePasting
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.RelativeDiscRealizationPowerCertificate

/-!
# Hull Lemma 4.9 branches from source Greendlinger certificates

This module applies Osin's source-faithful relative Greendlinger theorem to
the explicit power cactus.  The exterior cyclic arc is rebased at its initial
vertex, so the existing shortening, shadow, and prime-piece arguments apply
to a rotated shortest representative.

The long-period branch uses source constants `(1/4, 8*delta+2)`.  The bounded
loxodromic branch chooses an integral stable-power constant at least four and
uses `(1/M, 4*L)`.  In both cases the relator words satisfy the same source
constants by monotonicity from Hull's `(1/4,1)` condition.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- The dependent target carrier of an outer contiguity is definitionally the
outer dart cycle after its target option is identified with `none`. -/
theorem targetBoundaryDarts_eq_outerTargetArc
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : GGT.VanKampen.DiscDiagram.{u, w, 0} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : GGT.VanKampen.Embedded.Contiguity D eps Delta faces)
    (htarget : Gamma.target = none) :
    GGT.VanKampen.Embedded.targetBoundaryDarts Delta Gamma.target
        Gamma.targetArc = (Gamma.outerTargetArc htarget).darts := by
  cases Gamma with
  | mk _ _ target _ targetArc _ _ _ _ _ _ _ _ _ _ =>
      cases htarget
      rfl

/-! ## The long-period source branch -/

/-- Source Gr0 and the boundary equation of its embedded G-region rule out a
nontrivial power diagram with period at least `8*delta+2`. -/
theorem exists_parameters_false_of_longPeriod_powerDiagram_source
    (hgeom :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{u, w, 0})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (hpasting : HullLemma49SourceFacePastingStatement.{u, w}) :
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
  let b : ℕ := 8 * delta + 2
  have hbOne : (1 : ℝ) ≤ (b : ℕ) := by
    dsimp [b]
    exact_mod_cast (show 1 ≤ 8 * delta + 2 by omega)
  have hbNonneg : (0 : ℝ) ≤ (b : ℕ) := by positivity
  have hmuCertPos : (0 : ℝ) < 1 / 1000 := by norm_num
  have hmuCertUpper : (1 / 1000 : ℝ) ≤ 1 / 16 := by norm_num
  obtain ⟨epsCert, rho₀, _hrho₀, hcertificate⟩ :=
    GGT.VanKampen.lemma49Certificate_of_relativeGreendlinger
      hgeom D ⟨delta, hdelta⟩ (1 / 4) (b : ℝ) (1 / 1000)
        lemma49_sourceLambda_pos lemma49_sourceLambda_le_one hbNonneg
        hmuCertPos hmuCertUpper
  obtain ⟨K, hshadow⟩ :=
    exists_lemma49ContiguityShadow_constant delta epsCert
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
  have hbaseInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsCert (1 / 1000) rho₀ :=
    hfinalSym.mono_parameters hepsCert hmuMono hrho₀
  have hcondition := hbaseInput.toOsinCCondition_of_weakerConstants
    (le_refl (1 / 4 : ℝ)) hbOne
  have hboundary : GGT.VanKampen.IsLambdaCQuasiGeodesicWord D
      (1 / 4) (b : ℝ) (lemma49BoundaryPower Z.boundaryWord n) := by
    simpa only [b] using isLambdaCQuasiGeodesicWord_power_of_long_period
      D N hshort Z.boundary_geodesic
        Z.exponent_pos hdelta hlongPeriod
  obtain ⟨sourceCertificate⟩ :=
    hcertificate v g n Z hcondition hboundary
  have harcs : GGT.RelLetter.listVal
      (GGT.VanKampen.Embedded.dartWord sourceCertificate.diagram
        sourceCertificate.contiguity.sourceArc.darts) =
      GGT.RelLetter.listVal
          (GGT.VanKampen.Embedded.dartWord sourceCertificate.diagram
            sourceCertificate.contiguity.rightSide) *
        GGT.RelLetter.listVal
          (GGT.VanKampen.Embedded.dartWord sourceCertificate.diagram
            (sourceCertificate.contiguity.outerTargetArc
              sourceCertificate.target_eq).darts) *
        GGT.RelLetter.listVal
          (GGT.VanKampen.Embedded.dartWord sourceCertificate.diagram
            sourceCertificate.contiguity.leftSide) := by
    have h := sourceCertificate.contiguity.arcs_value_of_pasting
      (hpasting sourceCertificate)
    have htargetDarts := targetBoundaryDarts_eq_outerTargetArc
      sourceCertificate.contiguity sourceCertificate.target_eq
    rw [htargetDarts] at h
    exact h
  obtain ⟨E⟩ := exists_lemma49EmbeddedExteriorArc Z hbaseInput
    sourceCertificate.contiguity sourceCertificate.target_eq
      sourceCertificate.boundaryWord_eq hmuCertPos.le
      sourceCertificate.exterior_large harcs
  obtain ⟨rotated, Zrot, _conjugator, _hconjugate, _hconj, hword,
      hshortRot, C⟩ := E.exists_rebasedGreendlingerCell hshort
  obtain ⟨C⟩ := C
  have hlongRot : 8 * delta + 2 ≤ Zrot.boundaryWord.length := by
    rw [hword, List.length_rotate]
    exact hlongPeriod
  obtain ⟨Sh⟩ := hshadow G inferInstance Lambda D v rotated n rho Zrot C N
    inferInstance hdelta hcertInput hshortRot hlongRot
  apply false_of_longPeriod_powerDiagram_of_cell D Zrot C Sh hdelta
    hshortRot hcertInput hfinalSym
  · simpa only [b, scale] using hrhoScale
  · exact hconnectors
  · exact hlongRot

/-! ## The bounded loxodromic source branch -/

/-- Ordinary conjugacy transports loxodromy to the period obtained by cyclic
rebasing. -/
theorem isLoxodromic_of_inverse_conjugate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {g rotated conjugator : G}
    (hrotated : rotated = conjugator⁻¹ * g * conjugator)
    (hlox : IsLoxodromic g (Cayley.base D.alphabet)) :
    IsLoxodromic rotated (Cayley.base D.alphabet) := by
  rw [hrotated]
  simpa only [inv_inv] using
    (isLoxodromic_conj (isIsometricAction_cayley D.alphabet)
      (a := conjugator⁻¹) hlox)

/-- Source Gr0 with the stable-power boundary constants rules out every
bounded loxodromic period. -/
theorem exists_parameters_false_of_shortLoxodromic_powerDiagram_source
    (hgeom :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{u, w, 0})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {delta : ℕ}
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (hgap : CayleyUniformLoxodromicTranslationGap D.alphabet)
    (hpasting : HullLemma49SourceFacePastingStatement.{u, w}) :
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
  obtain ⟨M, hMFour, hLM⟩ :=
    exists_lemma49StablePowerConstant_four_le hd L
  have hM : 0 < M := lt_of_lt_of_le (by omega) hMFour
  have hsourceSlope : (1 / (M : ℝ)) ≤ 1 / 4 :=
    one_div_natCast_le_quarter hMFour
  have hsourceSlopePos : (0 : ℝ) < 1 / (M : ℝ) := by
    apply one_div_pos.mpr
    exact_mod_cast hM
  have hsourceSlopeUpper : (1 / (M : ℝ)) ≤ 1 :=
    le_trans hsourceSlope (by norm_num)
  let b : ℕ := 4 * L
  have hbOne : (1 : ℝ) ≤ (b : ℕ) := by
    dsimp [b]
    exact_mod_cast (show 1 ≤ 4 * L by omega)
  have hbNonneg : (0 : ℝ) ≤ (b : ℕ) := by positivity
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
  obtain ⟨epsCert, rho₀, _hrho₀, hcertificate⟩ :=
    GGT.VanKampen.lemma49Certificate_of_relativeGreendlinger
      hgeom D ⟨delta, hdelta⟩ (1 / (M : ℝ)) (b : ℝ) (1 / 1000)
        hsourceSlopePos hsourceSlopeUpper hbNonneg hmuCertPos hmuCertUpper
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
  have hfinalSym : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps mu rho := hinput.restrict_symmetrized hv
  have hcertInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsCert (1 / 1000) rho :=
    hfinalSym.mono_parameters hepsCert hmuCert le_rfl
  have hbaseInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsCert (1 / 1000) rho₀ :=
    hfinalSym.mono_parameters hepsCert hmuCert hrho₀
  have hcondition := hbaseInput.toOsinCCondition_of_weakerConstants
    hsourceSlope hbOne
  have hwordNe : Z.boundaryWord ≠ [] := by
    intro hnil
    have hg : g = 1 := by
      have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
        simpa using Z.boundary_geodesic.2.1
      rw [hnil] at hvalue
      exact hvalue.symm.trans GGT.RelLetter.listVal_nil
    exact Z.power_ne_one (by simp [hg])
  have hperiodPos : 0 < Z.boundaryWord.length :=
    List.length_pos_iff.mpr hwordNe
  have hlength : Z.boundaryWord.length ≤ L := by
    simpa only [L] using hshortPeriod
  have hdStable : d ≤ stableTranslation g (Cayley.base D.alphabet) :=
    le_trans hdd₀ (hgapAll g hlox)
  have hOneL : (1 : ℝ) ≤ (L : ℕ) := by exact_mod_cast hLPos
  have hdL : d ≤ (L : ℕ) := le_trans hdOne hOneL
  have hsourceBoundary : GGT.VanKampen.IsLambdaCQuasiGeodesicWord D
      (1 / (M : ℝ)) (b : ℝ)
      (lemma49BoundaryPower Z.boundaryWord n) := by
    simpa only [b] using
      isLambdaCQuasiGeodesicWord_power_of_stableTranslation D
        Z.boundary_geodesic hperiodPos hlength hM hd hdStable hdL hLM
  obtain ⟨sourceCertificate⟩ :=
    hcertificate v g n Z hcondition hsourceBoundary
  have harcs : GGT.RelLetter.listVal
      (GGT.VanKampen.Embedded.dartWord sourceCertificate.diagram
        sourceCertificate.contiguity.sourceArc.darts) =
      GGT.RelLetter.listVal
          (GGT.VanKampen.Embedded.dartWord sourceCertificate.diagram
            sourceCertificate.contiguity.rightSide) *
        GGT.RelLetter.listVal
          (GGT.VanKampen.Embedded.dartWord sourceCertificate.diagram
            (sourceCertificate.contiguity.outerTargetArc
              sourceCertificate.target_eq).darts) *
        GGT.RelLetter.listVal
          (GGT.VanKampen.Embedded.dartWord sourceCertificate.diagram
            sourceCertificate.contiguity.leftSide) := by
    have h := sourceCertificate.contiguity.arcs_value_of_pasting
      (hpasting sourceCertificate)
    have htargetDarts := targetBoundaryDarts_eq_outerTargetArc
      sourceCertificate.contiguity sourceCertificate.target_eq
    rw [htargetDarts] at h
    exact h
  obtain ⟨E⟩ := exists_lemma49EmbeddedExteriorArc Z hbaseInput
    sourceCertificate.contiguity sourceCertificate.target_eq
      sourceCertificate.boundaryWord_eq hmuCertPos.le
      sourceCertificate.exterior_large harcs
  obtain ⟨rotated, Zrot, conjugator, hconjugate, _hconj, hword,
      hshortRot, C⟩ := E.exists_rebasedGreendlingerCell hshort
  obtain ⟨C⟩ := C
  have hshortPeriodRot : Zrot.boundaryWord.length ≤ 8 * delta + 1 := by
    rw [hword, List.length_rotate]
    exact hshortPeriod
  have hloxRot : IsLoxodromic rotated (Cayley.base D.alphabet) :=
    isLoxodromic_of_inverse_conjugate D hconjugate hlox
  have hlongArc : 4 * Zrot.boundaryWord.length ≤
      3 * C.boundaryArc.length :=
    four_mul_period_le_three_mul_arc C hcertInput hshortScale hshortRot
  have hwordNeRot : Zrot.boundaryWord ≠ [] := by
    intro hnil
    have hg : rotated = 1 := by
      have hvalue : GGT.RelLetter.listVal Zrot.boundaryWord = rotated := by
        simpa using Zrot.boundary_geodesic.2.1
      rw [hnil] at hvalue
      exact hvalue.symm.trans GGT.RelLetter.listVal_nil
    exact Zrot.power_ne_one (by simp [hg])
  have hperiodPosRot : 0 < Zrot.boundaryWord.length :=
    List.length_pos_iff.mpr hwordNeRot
  have harcInfix : C.boundaryArc <:+:
      lemma49BoundaryPower Zrot.boundaryWord n :=
    ⟨C.boundaryBefore, C.boundaryAfter, C.boundary_decomposition.symm⟩
  obtain ⟨B⟩ := exists_scaledRepeatedBoundaryBlocks_of_lemma49PowerArc
    Zrot.exponent_pos harcInfix hperiodPosRot hdivisorSix hlongArc
  have hlengthRot : Zrot.boundaryWord.length ≤ L := by
    simpa only [L] using hshortPeriodRot
  have hdStableRot : d ≤
      stableTranslation rotated (Cayley.base D.alphabet) :=
    le_trans hdd₀ (hgapAll rotated hloxRot)
  have hPowerGlobal := isQuasiGeodesicChainAt_power_of_stableTranslation
    (n := n) D Zrot.boundary_geodesic hperiodPosRot hlengthRot hM hd
      hdStableRot hdL hLM
  obtain ⟨Sh⟩ := hshadow G inferInstance Lambda D v rotated n rho
    Zrot C hdelta hcertInput hPowerGlobal
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
