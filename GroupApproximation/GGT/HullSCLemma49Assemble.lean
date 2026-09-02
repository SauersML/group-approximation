import GroupApproximation.GGT.HullSCLemma49BowditchGap
import GroupApproximation.GGT.HullSCLemma49FixedDelta
import GroupApproximation.GGT.HullSCLemma49ShortPower
import GroupApproximation.GGT.HullSCLemma44CertificateInjectivity
import GroupApproximation.GGT.HullSCLemma49SourceAssembly
import GroupApproximation.GGT.HullSCLemma49InjectivityBridge
import GroupApproximation.GGT.VanKampen.Estimating.Assembly

/-!
# Assembly of Hull's Lemma 4.9 power-diagram statement

The relative Greendlinger certificate has three consequences for a shortest
power period.  A long period contradicts the fixed-scale prime-piece clause.
A short loxodromic period contradicts its scaled form, using Bowditch's
uniform stable-translation gap.  A non-loxodromic period has a short conjugate
power in the one-relator kernel, contradicting the ball-injectivity consequence
of the same relative Greendlinger theorem.

This module synchronizes the three parameter choices and proves the exact
`HullLemma49ShortestGeodesicPowerDiagramStatement`.  The only input is the one
shared relative Greendlinger proposition consumed by Hull Lemmas 4.4 and 4.9.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Synchronizing the three small-cancellation coefficients -/

/-- The minimum of the long-period, short-loxodromic, and injectivity
coefficients is positive. -/
theorem lemma49_commonMu_pos {muShort muInjective : ℝ}
    (hshort : 0 < muShort) (hinjective : 0 < muInjective) :
    0 < min (1 / 100000 : ℝ) (min muShort muInjective) := by
  rw [lt_min_iff, lt_min_iff]
  exact ⟨by norm_num, hshort, hinjective⟩

/-- The common coefficient is at most the one used by the long-period
branch. -/
theorem lemma49_commonMu_le_long (muShort muInjective : ℝ) :
    min (1 / 100000 : ℝ) (min muShort muInjective) ≤ 1 / 100000 :=
  min_le_left _ _

/-- The common coefficient is at most the one used by the short-loxodromic
branch. -/
theorem lemma49_commonMu_le_short (muShort muInjective : ℝ) :
    min (1 / 100000 : ℝ) (min muShort muInjective) ≤ muShort :=
  le_trans (min_le_right _ _) (min_le_left _ _)

/-- The common coefficient is at most the one used for ball injectivity. -/
theorem lemma49_commonMu_le_injective (muShort muInjective : ℝ) :
    min (1 / 100000 : ℝ) (min muShort muInjective) ≤ muInjective :=
  le_trans (min_le_right _ _) (min_le_right _ _)

/-! ## The three-case diagram argument -/

/-- The single relative Greendlinger proposition proves Hull's complete
shortest-geodesic power-diagram statement.  Bowditch Lemma 2.2 is discharged
from the supplied acylindricity, and all other inputs are consequences of the
same final `C₁` parameters. -/
theorem hullLemma49ShortestGeodesicPowerDiagram_of_relativeGreendlinger
    (hgeom : RelativeGreendlingerStatement.{u, w}) :
    HullLemma49ShortestGeodesicPowerDiagramStatement.{u, w} := by
  intro G _ Lambda D hemb hacylindrical
  obtain ⟨delta, hdelta⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  have hgap : CayleyUniformLoxodromicTranslationGap D.alphabet :=
    cayleyUniformLoxodromicTranslationGap_of_hyperbolicallyEmbedded
      D hemb hacylindrical
  obtain ⟨epsLong, rhoLong, hlong⟩ :=
    exists_parameters_false_of_longPeriod_powerDiagram_fixedDelta
      hgeom D hemb hdelta
  obtain ⟨epsShort, rhoShort, muShort, hmuShort,
      _hmuShortUpper, hshortLox⟩ :=
    exists_parameters_false_of_shortLoxodromic_powerDiagram_fixedDelta
      hgeom D hemb hdelta hgap
  let radius : ℕ := 8 * delta + 1
  obtain ⟨epsInjective, rhoInjective, muInjective, hmuInjective,
      hinjective⟩ :=
    exists_relativeBallInjectivityParameters_of_greendlinger
      hgeom D hemb radius
  let eps : ℕ := max epsLong (max epsShort epsInjective)
  let rho : ℕ := max rhoLong (max rhoShort rhoInjective)
  let mu : ℝ := min (1 / 100000 : ℝ) (min muShort muInjective)
  have hmu : 0 < mu := by
    dsimp [mu]
    exact lemma49_commonMu_pos hmuShort hmuInjective
  have hepsLong : epsLong ≤ eps := Nat.le_max_left _ _
  have hepsShort : epsShort ≤ eps :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hepsInjective : epsInjective ≤ eps :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hrhoLong : rhoLong ≤ rho := Nat.le_max_left _ _
  have hrhoShort : rhoShort ≤ rho :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrhoInjective : rhoInjective ≤ rho :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hmuLong : mu ≤ (1 / 100000 : ℝ) := by
    dsimp [mu]
    exact lemma49_commonMu_le_long muShort muInjective
  have hmuShort' : mu ≤ muShort := by
    dsimp [mu]
    exact lemma49_commonMu_le_short muShort muInjective
  have hmuInjective' : mu ≤ muInjective := by
    dsimp [mu]
    exact lemma49_commonMu_le_injective muShort muInjective
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hinput g n hshort Z
  have hlongInput : RelWord.IsLemma49Input D W epsLong
      (1 / 100000) rhoLong :=
    hinput.mono_parameters hepsLong hmuLong hrhoLong
  have hshortInput : RelWord.IsLemma49Input D W epsShort
      muShort rhoShort :=
    hinput.mono_parameters hepsShort hmuShort' hrhoShort
  by_cases hlox : IsLoxodromic g (Cayley.base D.alphabet)
  · by_cases hperiodLong : 8 * delta + 2 ≤ Z.boundaryWord.length
    · have hfalse : False :=
        hlong W v hv hlongInput g n hshort Z hperiodLong
      exact hfalse.elim
    · have hperiodShort : Z.boundaryWord.length ≤ 8 * delta + 1 := by
        omega
      have hfalse : False :=
        hshortLox W v hv hshortInput g n hshort hlox Z hperiodShort
      exact hfalse.elim
  · let N : Subgroup G :=
      Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
    letI : N.Normal := Subgroup.normalClosure_normal
    let quotientMap : G →* G ⧸ N := QuotientGroup.mk' N
    have hsymInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
        eps mu rho := hinput.restrict_symmetrized hv
    have hinjectiveInput : RelWord.IsLemma44Input D
        (RelWord.symmetrized v) epsInjective muInjective rhoInjective :=
      (hsymInput.mono_parameters hepsInjective hmuInjective'
        hrhoInjective).toIsLemma44Input
    have hker : quotientMap.ker =
        Subgroup.normalClosure
          (GGT.RelLetter.listVal '' RelWord.symmetrized v) := by
      dsimp [quotientMap]
      rw [QuotientGroup.ker_mk',
        RelWord.normalClosure_listVal_image_symmetrized]
    have hinj : Set.InjOn quotientMap
        (cayleyBall D.alphabet radius) :=
      hinjective (RelWord.symmetrized v) quotientMap hinjectiveInput hker
    have hfalse : False :=
      false_of_powerDiagram_of_not_isLoxodromic_of_ballInjective
        D Z hdelta hlox (by simpa only [radius] using hinj)
    exact hfalse.elim

/-! ## Source-faithful assembly -/

/-- The vk source certificate and the estimating-system construction assemble
the three cases of Hull's Lemma 4.9.  The face-pasting certificate is the
exact cellular callback consumed by the source power-diagram certificate, and
the injectivity callback is the exact hull44 output needed by the
non-loxodromic case. -/
theorem hullLemma49ShortestGeodesicPowerDiagram_of_estimating_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{0, 0, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundConstructionStatement.{0, 0, 0})
    (hpasting : HullLemma49SourceFacePastingStatement.{0, 0})
    (hinjective : HullLemma49InjectivityCallback.{0, 0}) :
    HullLemma49ShortestGeodesicPowerDiagramStatement.{0, 0} := by
  have hgeom :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{0, 0, 0} :=
    GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_components
      hselection hpieces hunbound
  apply hullLemma49ShortestGeodesicPowerDiagram_of_sourceBranches
  · exact hgeom
  · exact hpasting
  · exact hinjective

/-- End-to-end input leaf for the manuscript power-diagram statement.

The first four arguments are the current estimating interfaces: the common
relative Greendlinger statement and the three separated construction
certificates.  The next two are the kernel-geodesic and prefix-kernel outputs
of the Hull 4.4 assembly.  The final argument is vk's generic face-boundary
peeling callback; `hullLemma49SourceFacePastingStatement_of_faceSetBoundaryPeeling`
turns it into the source certificate consumed above. -/
theorem hullLemma49GeodesicPowerDiagram_of_inputs
    (hgeom : GGT.VanKampen.RelativeGreendlingerStatement.{0, 0})
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{0, 0, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundConstructionStatement.{0, 0, 0})
    (hkernel : KernelGeodesicEstimateStatement.{0, 0, 0})
    (htransfer : PrefixKernelConeTransferStatement.{0, 0, 0})
    (hfaceSetBoundaryPeeling :
      ∀ {G : Type} [Group G] {Lambda : Type}
        {W : Set (List (GGT.RelLetter G Lambda))}
        {Delta : GGT.VanKampen.DiscDiagram.{0, 0, 0} W}
        {faces : Finset Delta.toCombMap.Face}
        (boundary : GGT.VanKampen.Embedded.FaceSetBoundary Delta faces),
        GGT.VanKampen.Embedded.FaceSetBoundaryPeeling boundary) :
    HullLemma49ShortestGeodesicPowerDiagramStatement.{0, 0} := by
  have _hcanonical : HullLemma44CanonicalQuotientStatement.{0} :=
    hullLemma44CanonicalQuotientStatement_zero_of_relativeGreendlinger_of_kernelGeodesic_of_prefixTransfer
      hgeom hkernel htransfer
  have hpasting : HullLemma49SourceFacePastingStatement.{0, 0} :=
    hullLemma49SourceFacePastingStatement_of_faceSetBoundaryPeeling
      hfaceSetBoundaryPeeling
  have hinjective : HullLemma49InjectivityCallback.{0, 0} :=
    hullLemma49InjectivityCallback_of_relativeGreendlinger hgeom
  exact hullLemma49ShortestGeodesicPowerDiagram_of_estimating_components
    hselection hpieces hunbound hpasting hinjective

/-- The same input leaf using the currently landed vk shape.  vk's named
`faceSetBoundaryPeeling_of_faceSetBoundary` consumes the displayed local
`FaceSetBoundaryPeelOracle`; the Hull49 bridge applies it to each selected
source certificate. -/
theorem hullLemma49GeodesicPowerDiagram_of_inputs_of_vkOracle
    (hgeom : GGT.VanKampen.RelativeGreendlingerStatement.{0, 0})
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{0, 0, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundConstructionStatement.{0, 0, 0})
    (hkernel : KernelGeodesicEstimateStatement.{0, 0, 0})
    (htransfer : PrefixKernelConeTransferStatement.{0, 0, 0})
    (horacle :
      ∀ {G : Type} [Group G] {Lambda : Type}
        {W : Set (List (GGT.RelLetter G Lambda))}
        {Delta : GGT.VanKampen.DiscDiagram.{0, 0, 0} W},
        GGT.VanKampen.Embedded.FaceSetBoundaryPeelOracle
          (Delta := Delta)) :
    HullLemma49ShortestGeodesicPowerDiagramStatement.{0, 0} := by
  have _hcanonical : HullLemma44CanonicalQuotientStatement.{0} :=
    hullLemma44CanonicalQuotientStatement_zero_of_relativeGreendlinger_of_kernelGeodesic_of_prefixTransfer
      hgeom hkernel htransfer
  have hpasting : HullLemma49SourceFacePastingStatement.{0, 0} :=
    hullLemma49SourceFacePastingStatement_of_vkFaceSetBoundaryPeeling horacle
  have hinjective : HullLemma49InjectivityCallback.{0, 0} :=
    hullLemma49InjectivityCallback_of_relativeGreendlinger hgeom
  exact hullLemma49ShortestGeodesicPowerDiagram_of_estimating_components
    hselection hpieces hunbound hpasting hinjective

/-! ## Model check -/

/-- In the one-point group the exact power-diagram conclusion holds because
the diagram's required nontrivial outer power is impossible. -/
theorem hullLemma49ShortestGeodesicPowerDiagram_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    ∀ (v : List (GGT.RelLetter PUnit Lambda)) (n : ℕ),
      Lemma49GeodesicPowerDiagram D v 1 n →
        ∃ k ∈ Subgroup.normalClosure
            ({GGT.RelLetter.listVal v} : Set PUnit),
          (1 * k) ^ n = 1 := by
  intro v n Z
  exact (Z.power_ne_one (Subsingleton.elim _ _)).elim

end HullSC
end GroupApproximation
