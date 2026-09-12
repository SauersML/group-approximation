import GroupApproximation.GGT.VanKampen.Estimating.OsinAppendixSections
import GroupApproximation.GGT.HullSCRelativeLeastAreaDiagram
import GroupApproximation.GGT.HullSCLemma49LeastAreaPowerDiagram
import GroupApproximation.GGT.HullSCRelativeGreendlingerGeodesicConsumers
import GroupApproximation.GGT.HullSCLemma44QuasiGeodesicBridge
import GroupApproximation.GGT.HullSCLemma49SourceAssembly
import GroupApproximation.GGT.HullSCLemma49PowerDiagramFromComponents
import GroupApproximation.GGT.VanKampen.RelativeDiscRealizationPowerCertificate
import GroupApproximation.Meta.AxiomGuard

/-!
# The Hull consumers at the least-area Greendlinger waist

`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement` is Osin's
Lemma 4.4 at least-area planar diagrams (`DiscDiagram.LeastArea`), which is
what Osin's proof gives.  Least area is strictly stronger than the algebraic
`DiscDiagram.Reduced` the historical waist asks for, so nothing implies the
historical waist from it, and every consumer has to move once.  This module
is that move, as **twins**: each theorem below is the existing one with its
diagrams restricted to least-area ones, and its body is the existing proof with
the planar least-area fact passed where `reduced` was.

* Lemma 4.4 side: the spelling waist and the geodesic-length waist over
  `HullSC.RelativeLeastAreaDiagram`, the ball-injectivity consumers, and the
  Lemma 4.9 injectivity callback.  Every diagram those consumers produce is a
  Hull Lemma 4.4 diagram, which carries `area_minimal`
  (`Lemma44OrientedRelatorDiagram.toRelativeLeastAreaDiagram`).
* Lemma 4.9 side: the certificate on the explicit power cactus, the long-period
  and bounded-loxodromic branches, the three-case assembly and the kernel-power
  statement, over `HullSC.Lemma49LeastAreaPowerDiagram`, whose producer keeps
  the minimality (`exists_lemma49LeastAreaPowerDiagram`).
-/

namespace GroupApproximation

universe u w

namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

/-- **Source Greendlinger on the power cactus, at the least-area waist.**  The
existing `lemma49Certificate_of_relativeGreendlinger`, over least-area power
diagrams; the planar least area of the cactus is
`Lemma49LeastAreaPowerDiagram.cactus_leastArea`. -/
theorem lemma49Certificate_of_relativeGreendlingerLeastArea
    (hgeom : RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, 0})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lambda c mu : ℝ)
    (hlambda : 0 < lambda) (hlambdaUpper : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho : ℕ, 0 < rho ∧
      ∀ (v : List (GGT.RelLetter G Lambda)) (g : G) (n : ℕ)
        (Z : HullSC.Lemma49LeastAreaPowerDiagram D v g n),
        OsinCCondition D (RelWord.symmetrized v) eps mu lambda c rho →
        IsLambdaCQuasiGeodesicWord D lambda c
          (lemma49BoundaryPower Z.boundaryWord n) →
        Nonempty
          (Lemma49SourceGreendlingerCertificate D v g n eps mu
            Z.toLemma49GeodesicPowerDiagram) := by
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    hgeom D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro v g n Z hcondition hboundary
  let realization := relativeDiscRealizationPower D Z.toLemma49GeodesicPowerDiagram
  have hboundary' : IsLambdaCQuasiGeodesicWord D lambda c
      realization.diagram.boundaryWord := by
    rw [realization.outerWord_eq]
    exact hboundary
  have hcells : 0 < realization.diagram.rCellCount := by
    exact relativeDiscRealizationPower_rCellCount_pos D Z.toLemma49GeodesicPowerDiagram
  have hlea : realization.diagram.LeastArea := fun hm => Z.cactus_leastArea hm
  obtain ⟨diagram, hequivalent, faces, contiguity, htarget, hlarge⟩ :=
    hgood (RelWord.symmetrized v) hcondition realization.diagram
      hlea hcells hboundary'
  obtain ⟨equivalent⟩ := hequivalent
  have hdiagramBoundary : diagram.boundaryWord =
      lemma49BoundaryPower Z.boundaryWord n :=
    equivalent.boundaryWord_eq.trans realization.outerWord_eq
  exact ⟨{
    realization := realization
    diagram := diagram
    equivalent := ⟨equivalent⟩
    boundaryWord_eq := hdiagramBoundary
    faces := faces
    contiguity := contiguity
    target_eq := htarget
    exterior_large := hlarge }⟩

end VanKampen
end GGT

namespace HullSC

/-! ## Lemma 4.4 side -/

section LemmaFourFour

open GroupApproximation.GGT.VanKampen
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- **Osin's Lemma 4.4 in certificate form at least-area diagrams with a
quasi-geodesic spelling**: `RelativeGreendlingerQuasiGeodesicSpellingStatement`
with the diagrams restricted to `RelativeLeastAreaDiagram`. -/
def RelativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
            RelWord.IsLemma44Input D W eps mu rho →
              ∀ Z : RelativeLeastAreaDiagram D W R,
                Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
                  Nonempty
                    (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram)

/-- **The spelling waist at least area**, from the least-area Greendlinger
statement: `relativeGreendlingerQuasiGeodesicSpellingStatement_of_greendlinger`
passing the planar least area of the cactus
(`RelativeDiscRealizationAtWord.leastArea`) where `reduced` was. -/
theorem relativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement_of_leastAreaGreendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, 0})
    (hreal : RelativeDiscRealizationSpellingStatement.{u, w})
    (hconv : RelativeExteriorArcConversionAtWordRotatedStatement.{u, w}) :
    RelativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  have hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hD
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    hgreendlinger D hhyper (1 / 4) 1 mu
      (by norm_num) (by norm_num) (by norm_num) hmu hmuUpper
  refine ⟨eps, rho, ?_⟩
  intro rho' hrho' W R hinput Z hspell
  have hinput0 : RelWord.IsLemma44Input D W eps mu rho :=
    hinput.mono_parameters le_rfl le_rfl hrho'
  have hcondition :
      GGT.VanKampen.OsinCCondition D W eps mu (1 / 4) 1 rho :=
    hinput0.toOsinCCondition
  obtain ⟨outer, hmap, houterVal, hqgOuter⟩ := hspell
  obtain ⟨Creal⟩ := hreal D W R Z.toRelativeReducedDiagram outer hmap
  have hqg : IsLambdaCQuasiGeodesicWord D (1 / 4) 1
      Creal.diagram.boundaryWord := by
    rw [Creal.outerWord_eq]
    exact hqgOuter
  have hlea : Creal.diagram.LeastArea := fun hm => Creal.leastArea Z houterVal hm
  obtain ⟨Delta, hequivNonempty, faces, Gamma, htarget, hlarge⟩ :=
    hgood W hcondition Creal.diagram hlea Creal.rCellCount_pos hqg
  obtain ⟨hequiv⟩ := hequivNonempty
  have hboundaryWord : Delta.boundaryWord = outer :=
    hequiv.boundaryWord_eq.trans Creal.outerWord_eq
  let packaged : EmbeddedBoundaryContiguity D eps Delta Gamma.source :=
    { faces := faces
      region := Gamma
      source_eq := rfl
      target_eq := htarget }
  have hword : (GGT.VanKampen.Embedded.cell Delta Gamma.source).word =
      (Z.cells.get
        (Creal.cellIndex.symm (hequiv.cellIndex.symm Gamma.source))).relator :=
    cellWord_eq_relator_of_oEquivalent_atWord Creal hequiv Gamma.source
  obtain ⟨n, C, hC⟩ :=
    hconv D eps Delta Z.boundaryWord outer hboundaryWord hmap Gamma.source
      packaged
      ((Z.cells.get
        (Creal.cellIndex.symm (hequiv.cellIndex.symm Gamma.source))).relator)
      hword
  refine ⟨RelativeDiagramCertificate.ofLargeCellRotated hinput.rotate_mem
    (Creal.cellIndex.symm (hequiv.cellIndex.symm Gamma.source)) n C ?_⟩
  simp only [List.length_rotate]
  have hlengthEq :
      (((Z.cells.get
          (Creal.cellIndex.symm
            (hequiv.cellIndex.symm Gamma.source))).relator).length : ℝ) =
        (((GGT.VanKampen.Embedded.cell Delta Gamma.source).word).length : ℝ) := by
    rw [hword]
  have hstep :
      (1 - 23 * mu) *
          (((GGT.VanKampen.Embedded.cell Delta Gamma.source).word).length : ℝ)
        ≤ (1 - 13 * mu) *
          (((GGT.VanKampen.Embedded.cell Delta Gamma.source).word).length : ℝ) :=
    mul_le_mul_of_twentyThree_le_thirteen hmu.le _
  have hCreal : (Gamma.sourceArc.length : ℝ) ≤ (C.exterior.length : ℝ) :=
    Nat.cast_le.mpr hC
  rw [hlengthEq]
  exact le_trans hstep (le_trans (le_of_lt hlarge) hCreal)

/-- **Osin's Lemma 4.4 in certificate form at least-area diagrams whose
designated boundary word is geodesic in the relative alphabet.** -/
def RelativeGreendlingerGeodesicLengthLeastAreaStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
            RelWord.IsLemma44Input D W eps mu rho →
              ∀ Z : RelativeLeastAreaDiagram D W R,
                Z.toRelativeReducedDiagram.HasGeodesicBoundaryLength →
                  Nonempty
                    (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram)

/-- **The geodesic-length waist at least area**, from the least-area Greendlinger
statement: `relativeGreendlingerGeodesicLengthStatement_of_greendlinger` with
the planar least area passed where `reduced` was. -/
theorem relativeGreendlingerGeodesicLengthLeastAreaStatement_of_leastAreaGreendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, 0})
    (hreal : RelativeDiscRealizationSpellingStatement.{u, w})
    (hconv : RelativeExteriorArcConversionAtWordRotatedStatement.{u, w}) :
    RelativeGreendlingerGeodesicLengthLeastAreaStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  have hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hD
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    hgreendlinger D hhyper (1 / 4) 1 mu
      (by norm_num) (by norm_num) (by norm_num) hmu hmuUpper
  refine ⟨eps, rho, ?_⟩
  intro rho' hrho' W R hinput Z hgeo
  have hinput0 : RelWord.IsLemma44Input D W eps mu rho :=
    hinput.mono_parameters le_rfl le_rfl hrho'
  have hcondition :
      GGT.VanKampen.OsinCCondition D W eps mu (1 / 4) 1 rho :=
    hinput0.toOsinCCondition
  obtain ⟨outer, houter, hmap⟩ :=
    exists_geodesicSpelling_of_hasGeodesicBoundaryLength Z.toRelativeReducedDiagram hgeo
  have houterVal : GGT.RelLetter.listVal outer = Z.boundary := by
    simpa using houter.2.1
  obtain ⟨Creal⟩ := hreal D W R Z.toRelativeReducedDiagram outer hmap
  have hqg : IsLambdaCQuasiGeodesicWord D (1 / 4) 1 Creal.diagram.boundaryWord := by
    rw [Creal.outerWord_eq]
    exact isLambdaCQuasiGeodesicWord_of_isGeodesicWord D houter
      (by norm_num) (by norm_num)
  have hlea : Creal.diagram.LeastArea := fun hm => Creal.leastArea Z houterVal hm
  obtain ⟨Delta, hequivNonempty, faces, Gamma, htarget, hlarge⟩ :=
    hgood W hcondition Creal.diagram hlea Creal.rCellCount_pos hqg
  obtain ⟨hequiv⟩ := hequivNonempty
  have hboundaryWord : Delta.boundaryWord = outer :=
    hequiv.boundaryWord_eq.trans Creal.outerWord_eq
  let packaged : EmbeddedBoundaryContiguity D eps Delta Gamma.source :=
    { faces := faces
      region := Gamma
      source_eq := rfl
      target_eq := htarget }
  have hword : (GGT.VanKampen.Embedded.cell Delta Gamma.source).word =
      (Z.cells.get
        (Creal.cellIndex.symm (hequiv.cellIndex.symm Gamma.source))).relator :=
    cellWord_eq_relator_of_oEquivalent_atWord Creal hequiv Gamma.source
  obtain ⟨n, C, hC⟩ :=
    hconv D eps Delta Z.boundaryWord outer hboundaryWord hmap Gamma.source
      packaged
      ((Z.cells.get
        (Creal.cellIndex.symm (hequiv.cellIndex.symm Gamma.source))).relator)
      hword
  refine ⟨RelativeDiagramCertificate.ofLargeCellRotated hinput.rotate_mem
    (Creal.cellIndex.symm (hequiv.cellIndex.symm Gamma.source)) n C ?_⟩
  simp only [List.length_rotate]
  have hlengthEq :
      (((Z.cells.get
          (Creal.cellIndex.symm
            (hequiv.cellIndex.symm Gamma.source))).relator).length : ℝ) =
        (((GGT.VanKampen.Embedded.cell Delta Gamma.source).word).length : ℝ) := by
    rw [hword]
  have hstep :
      (1 - 23 * mu) *
          (((GGT.VanKampen.Embedded.cell Delta Gamma.source).word).length : ℝ)
        ≤ (1 - 13 * mu) *
          (((GGT.VanKampen.Embedded.cell Delta Gamma.source).word).length : ℝ) :=
    mul_le_mul_of_twentyThree_le_thirteen hmu.le _
  have hCreal : (Gamma.sourceArc.length : ℝ) ≤ (C.exterior.length : ℝ) :=
    Nat.cast_le.mpr hC
  rw [hlengthEq]
  exact le_trans hstep (le_trans (le_of_lt hlarge) hCreal)

/-- `injOn_relativeBall_of_geodesicLengthCertificates` with certificates asked
only at least-area diagrams.  The diagram the proof produces is a Hull Lemma 4.4
diagram, which is least area. -/
theorem injOn_relativeBall_of_geodesicLengthLeastAreaCertificates
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ Z : RelativeLeastAreaDiagram D W R,
      Z.toRelativeReducedDiagram.HasGeodesicBoundaryLength →
        Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram)) :
    Set.InjOn q (cayleyBall D.alphabet R) := by
  by_contra hnot
  obtain ⟨Z0⟩ := exists_lemma44ReducedRelatorDiagram_of_not_injOn
    D.alphabet W R q hker hnot
  obtain ⟨Z⟩ := Z0.exists_oriented hsc.toIsSmallCancellation
  obtain ⟨K⟩ := hcert (Z.toRelativeLeastAreaDiagram D)
    (hasGeodesicBoundaryLength_toRelativeReducedDiagram D Z)
  exact false_of_relativeDiagramCertificate D Z hsc hmu hthreshold K

/-- `exists_relativeBallInjectivityParameters_of_geodesicLengthGreendlinger` at
the least-area statement; the numerical choices are the original's. -/
theorem exists_relativeBallInjectivityParameters_of_geodesicLengthLeastAreaGreendlinger
    (hgeom : RelativeGreendlingerGeodesicLengthLeastAreaStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (R : ℕ) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        {Q : Type*} [Group Q] (q : G →* Q),
        RelWord.IsLemma44Input D W eps mu rho →
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Set.InjOn q (cayleyBall D.alphabet R) := by
  let mu : ℝ := 1 / 100
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuNinetyTwo : mu ≤ 1 / 92 := by
    dsimp [mu]
    norm_num
  obtain ⟨eps, rho0, hgood⟩ := hgeom D hemb mu hmuPos hmuSixteen
  let boundaryScale : ℕ := 2 * R + 2 * eps + 1
  let rho : ℕ := max rho0 (8 * boundaryScale)
  have hrho0 : rho0 ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * boundaryScale ≤ rho := Nat.le_max_right _ _
  have hscalePos : (0 : ℝ) < (boundaryScale : ℝ) := by
    dsimp [boundaryScale]
    positivity
  have hrhoScaleReal : (8 : ℝ) * (boundaryScale : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrhoScale
  have hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ) := by
    change 4 * (boundaryScale : ℝ) < (3 / 4 : ℝ) * (rho : ℝ)
    nlinarith
  refine ⟨eps, rho, mu, hmuPos, ?_⟩
  intro W Q _ q hsc hker
  exact injOn_relativeBall_of_geodesicLengthLeastAreaCertificates D hsc hmuNinetyTwo
    hthreshold q hker (fun Z hZ => hgood rho hrho0 W R hsc Z hZ)

/-- **The Lemma 4.9 injectivity callback from the least-area geodesic-length
statement.** -/
theorem hullLemma49InjectivityCallback_of_geodesicLengthLeastAreaGreendlinger
    (hgeom : RelativeGreendlingerGeodesicLengthLeastAreaStatement.{u, w}) :
    HullLemma49InjectivityCallback.{u, w} := by
  intro G _ Lambda D hD delta _hdelta
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    exists_relativeBallInjectivityParameters_of_geodesicLengthLeastAreaGreendlinger
      hgeom D hD (8 * delta + 1)
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hker
  exact hgood W q hinput.toIsLemma44Input hker

/-- `injOn_relativeBall_of_quasiGeodesicCertificates` with certificates at
least-area diagrams only. -/
theorem injOn_relativeBall_of_quasiGeodesicLeastAreaCertificates
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * R + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ Z : RelativeLeastAreaDiagram D W R,
      Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram)) :
    Set.InjOn q (cayleyBall D.alphabet R) :=
  injOn_relativeBall_of_geodesicLengthLeastAreaCertificates D hsc hmu hthreshold q hker
    (fun Z hZ =>
      hcert Z (hasQuasiGeodesicSpelling_of_hasGeodesicBoundaryLength
        Z.toRelativeReducedDiagram hZ))

/-- `injOn_ball_and_peripheralUnion_of_quasiGeodesicCertificates` with
certificates at least-area diagrams only; the proof is the original one with
the least-area ball theorem substituted. -/
theorem injOn_ball_and_peripheralUnion_of_quasiGeodesicLeastAreaCertificates
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (A : Alphabet G)
    (hA : A.carrier ⊆ D.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 92)
    (hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ))
    {Q : Type*} [Group Q] (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ Z : RelativeLeastAreaDiagram D W (max R 1),
      Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D W eps mu Z.toRelativeReducedDiagram)) :
    Set.InjOn q (cayleyBall A R) ∧
      Set.InjOn q (⋃ i : Lambda, (D.fam i : Set G)) := by
  have hinj : Set.InjOn q (cayleyBall D.alphabet (max R 1)) :=
    injOn_relativeBall_of_quasiGeodesicLeastAreaCertificates D hsc hmu hthreshold q hker
      hcert
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    apply hinj
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_left R 1)
      exact cayleyBall_subset_of_alphabet_subset A D.alphabet hA R hx
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_left R 1)
      exact cayleyBall_subset_of_alphabet_subset A D.alphabet hA R hy
    · exact hxy
  · apply injOn_peripheralUnion_of_injOn_cayleyBall_one D q
    intro x hx y hy hxy
    apply hinj
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_right R 1)
      exact hx
    · apply cayleyBall_subset_of_le_radius D.alphabet
        (Nat.le_max_right R 1)
      exact hy
    · exact hxy

end LemmaFourFour

/-! ## Lemma 4.9 side -/

section LemmaFourNine

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

/-- `exists_parameters_false_of_longPeriod_powerDiagram_source` at the least-area
waist, over least-area power diagrams. -/
theorem exists_parameters_false_of_longPeriod_leastAreaPowerDiagram_source
    (hgeom :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, 0})
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
            ∀ Z : Lemma49LeastAreaPowerDiagram D v g n,
              8 * delta + 2 ≤ Z.boundaryWord.length → False := by
  let b : ℕ := 8 * delta + 2
  have hbOne : (1 : ℝ) ≤ (b : ℕ) := by
    dsimp [b]
    exact_mod_cast (show 1 ≤ 8 * delta + 2 by omega)
  have hbNonneg : (0 : ℝ) ≤ (b : ℕ) := by positivity
  have hmuCertPos : (0 : ℝ) < 1 / 1000 := by norm_num
  have hmuCertUpper : (1 / 1000 : ℝ) ≤ 1 / 16 := by norm_num
  obtain ⟨epsCert, rho₀, _hrho₀, hcertificate⟩ :=
    GGT.VanKampen.lemma49Certificate_of_relativeGreendlingerLeastArea
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
  obtain ⟨E⟩ := exists_lemma49EmbeddedExteriorArc Z.toLemma49GeodesicPowerDiagram
    hbaseInput sourceCertificate.contiguity sourceCertificate.target_eq
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

/-- `exists_parameters_false_of_shortLoxodromic_powerDiagram_source` at the
least-area waist, over least-area power diagrams. -/
theorem exists_parameters_false_of_shortLoxodromic_leastAreaPowerDiagram_source
    (hgeom :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, 0})
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
            ∀ Z : Lemma49LeastAreaPowerDiagram D v g n,
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
    GGT.VanKampen.lemma49Certificate_of_relativeGreendlingerLeastArea
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
  obtain ⟨E⟩ := exists_lemma49EmbeddedExteriorArc Z.toLemma49GeodesicPowerDiagram
    hbaseInput sourceCertificate.contiguity sourceCertificate.target_eq
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

/-- **Hull's shortest-geodesic power-diagram statement over least-area power
diagrams.**  `HullLemma49ShortestGeodesicPowerDiagramStatement` with the power
diagram least area; the kernel-power statement follows from it because the
diagram the proof builds is least area (`exists_lemma49LeastAreaPowerDiagram`). -/
def HullLemma49ShortestGeodesicLeastAreaPowerDiagramStatement : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w} [Finite Λ]
    (D : GGT.RelGenSet G Λ),
    D.IsHyperbolicallyEmbedded → IsAcylindrical G (Cayley D.alphabet) →
      ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
        ∀ (W : Set (List (GGT.RelLetter G Λ)))
          (v : List (GGT.RelLetter G Λ)), v ∈ W →
          RelWord.IsLemma49Input D W eps mu rho →
            ∀ (g : G) (n : ℕ),
              IsShortestModuloConjugacy D.alphabet.carrier
                (Subgroup.normalClosure
                  ({GGT.RelLetter.listVal v} : Set G)) g →
              Lemma49LeastAreaPowerDiagram D v g n →
                ∃ k ∈ Subgroup.normalClosure
                    ({GGT.RelLetter.listVal v} : Set G),
                  (g * k) ^ n = 1

/-- `hullLemma49ShortestGeodesicPowerDiagram_of_sourceBranches` at the
least-area waist; the three-case argument is unchanged. -/
theorem hullLemma49ShortestGeodesicLeastAreaPowerDiagram_of_sourceBranches
    (hgeom :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{u, w, 0})
    (hpasting : HullLemma49SourceFacePastingStatement.{u, w})
    (hinjective : HullLemma49InjectivityCallback.{u, w}) :
    HullLemma49ShortestGeodesicLeastAreaPowerDiagramStatement.{u, w} := by
  intro G _ Lambda _ D hemb hacylindrical
  obtain ⟨delta, hdelta⟩ :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hemb
  have hgap : CayleyUniformLoxodromicTranslationGap D.alphabet :=
    cayleyUniformLoxodromicTranslationGap_of_hyperbolicallyEmbedded
      D hemb hacylindrical
  obtain ⟨epsLong, rhoLong, hlong⟩ :=
    exists_parameters_false_of_longPeriod_leastAreaPowerDiagram_source
      hgeom D hdelta hpasting
  obtain ⟨epsShort, rhoShort, muShort, hmuShort, _hmuShortUpper,
      hshortLox⟩ :=
    exists_parameters_false_of_shortLoxodromic_leastAreaPowerDiagram_source
      hgeom D hdelta hgap hpasting
  obtain ⟨epsInjective, rhoInjective, muInjective, hmuInjective,
      hinjAll⟩ := hinjective D hemb delta hdelta
  let eps : ℕ := max epsLong (max epsShort epsInjective)
  let rho : ℕ := max rhoLong (max rhoShort rhoInjective)
  let mu : ℝ := min (1 / 100000 : ℝ) (min muShort muInjective)
  have hcommon := sourceLemma49_commonMu_bounds hmuShort hmuInjective
  have hmu : 0 < mu := by
    dsimp [mu]
    exact hcommon.1
  have hepsLong : epsLong ≤ eps := Nat.le_max_left _ _
  have hepsShort : epsShort ≤ eps :=
    sourceLemma49_middle_le_nestedMax epsLong epsShort epsInjective
  have hepsInjective : epsInjective ≤ eps :=
    sourceLemma49_last_le_nestedMax epsLong epsShort epsInjective
  have hrhoLong : rhoLong ≤ rho := Nat.le_max_left _ _
  have hrhoShort : rhoShort ≤ rho :=
    sourceLemma49_middle_le_nestedMax rhoLong rhoShort rhoInjective
  have hrhoInjective : rhoInjective ≤ rho :=
    sourceLemma49_last_le_nestedMax rhoLong rhoShort rhoInjective
  have hmuLong : mu ≤ (1 / 100000 : ℝ) := by
    dsimp [mu]
    exact hcommon.2.1
  have hmuShort' : mu ≤ muShort := by
    dsimp [mu]
    exact hcommon.2.2.1
  have hmuInjective' : mu ≤ muInjective := by
    dsimp [mu]
    exact hcommon.2.2.2
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
    · exact (hlong W v hv hlongInput g n hshort Z hperiodLong).elim
    · have hperiodShort : Z.boundaryWord.length ≤ 8 * delta + 1 := by
        exact sourceLemma49_shortPeriod_of_not_long hperiodLong
      exact (hshortLox W v hv hshortInput g n hshort hlox Z hperiodShort).elim
  · let N : Subgroup G :=
      Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
    letI : N.Normal := Subgroup.normalClosure_normal
    let quotientMap : G →* G ⧸ N := QuotientGroup.mk' N
    have hsymInput : RelWord.IsLemma49Input D
        (RelWord.symmetrized v) eps mu rho := hinput.restrict_symmetrized hv
    have hinjectiveInput : RelWord.IsLemma49Input D
        (RelWord.symmetrized v) epsInjective muInjective rhoInjective :=
      (hsymInput.mono_parameters hepsInjective hmuInjective'
        hrhoInjective)
    have hker : quotientMap.ker =
        Subgroup.normalClosure
          (GGT.RelLetter.listVal '' RelWord.symmetrized v) := by
      dsimp [quotientMap]
      rw [QuotientGroup.ker_mk',
        RelWord.normalClosure_listVal_image_symmetrized]
    have hinjBall : Set.InjOn quotientMap
        (cayleyBall D.alphabet (8 * delta + 1)) := by
      apply hinjAll (W := RelWord.symmetrized v) (q := quotientMap)
      · exact hinjectiveInput
      · exact hker
    exact (false_of_powerDiagram_of_not_isLoxodromic_of_ballInjective
      D Z.toLemma49GeodesicPowerDiagram hdelta hlox hinjBall).elim

/-- **The kernel-power statement from the least-area power-diagram statement**:
`hullLemma49KernelPowerStatement_of_geodesicPowerDiagram`, building the least-area
diagram with `exists_lemma49LeastAreaPowerDiagram`. -/
theorem hullLemma49KernelPowerStatement_of_leastAreaPowerDiagram
    (hdiagram : HullLemma49ShortestGeodesicLeastAreaPowerDiagramStatement.{u, w}) :
    HullLemma49KernelPowerStatement.{u, w} := by
  intro G _ Λ _ D hemb hacy
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hdiagram D hemb hacy
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hinput g n hn hpow
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  obtain ⟨h, hgh, hshort⟩ :=
    exists_shortest_conjugateModulo D.alphabet.carrier N g
  have hhpow : h ^ n ∈ N := hgh.pow_mem hpow
  have hcorr : ∃ k ∈ N, (h * k) ^ n = 1 := by
    by_cases htrivial : h ^ n = 1
    · exact ⟨1, N.one_mem, by simpa using htrivial⟩
    · obtain ⟨P⟩ := exists_lemma49LeastAreaPowerDiagram D hn hhpow htrivial
      exact hgood W v hv hinput h n hshort P
  exact hgh.correction hcorr

/-- **Hull's Lemma 4.9 power-diagram leaf at the least-area waist.**  The face
pasting and the realization at a supplied spelling are theorems; the
exterior-arc conversion is the landed theorem, and the injectivity callback
comes from the least-area geodesic-length waist. -/
theorem hullLemma49ShortestGeodesicLeastAreaPowerDiagram_of_leastAreaGreendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullLemma49ShortestGeodesicLeastAreaPowerDiagramStatement.{0, 0} :=
  hullLemma49ShortestGeodesicLeastAreaPowerDiagram_of_sourceBranches hgreendlinger
    hullLemma49SourceFacePastingStatement_holds
    (hullLemma49InjectivityCallback_of_geodesicLengthLeastAreaGreendlinger
      (relativeGreendlingerGeodesicLengthLeastAreaStatement_of_leastAreaGreendlinger
        hgreendlinger relativeDiscRealizationSpellingStatement
        relativeExteriorArcConversionAtWordRotatedStatement))

/-- **Hull's Lemma 4.9 kernel-power correction from the least-area Greendlinger
waist alone.** -/
theorem hullLemma49KernelPowerStatement_of_leastAreaGreendlinger
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0}) :
    HullLemma49KernelPowerStatement.{0, 0} :=
  hullLemma49KernelPowerStatement_of_leastAreaPowerDiagram
    (hullLemma49ShortestGeodesicLeastAreaPowerDiagram_of_leastAreaGreendlinger
      hgreendlinger)

end LemmaFourNine

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.GGT.VanKampen.lemma49Certificate_of_relativeGreendlingerLeastArea
#audit_axioms GroupApproximation.HullSC.relativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement_of_leastAreaGreendlinger
#audit_axioms GroupApproximation.HullSC.relativeGreendlingerGeodesicLengthLeastAreaStatement_of_leastAreaGreendlinger
#audit_axioms GroupApproximation.HullSC.injOn_relativeBall_of_geodesicLengthLeastAreaCertificates
#audit_axioms GroupApproximation.HullSC.exists_relativeBallInjectivityParameters_of_geodesicLengthLeastAreaGreendlinger
#audit_axioms GroupApproximation.HullSC.hullLemma49InjectivityCallback_of_geodesicLengthLeastAreaGreendlinger
#audit_axioms GroupApproximation.HullSC.injOn_relativeBall_of_quasiGeodesicLeastAreaCertificates
#audit_axioms GroupApproximation.HullSC.injOn_ball_and_peripheralUnion_of_quasiGeodesicLeastAreaCertificates
#audit_axioms GroupApproximation.HullSC.exists_parameters_false_of_longPeriod_leastAreaPowerDiagram_source
#audit_axioms GroupApproximation.HullSC.exists_parameters_false_of_shortLoxodromic_leastAreaPowerDiagram_source
#audit_axioms GroupApproximation.HullSC.hullLemma49ShortestGeodesicLeastAreaPowerDiagram_of_sourceBranches
#audit_axioms GroupApproximation.HullSC.hullLemma49KernelPowerStatement_of_leastAreaPowerDiagram
#audit_axioms GroupApproximation.HullSC.hullLemma49ShortestGeodesicLeastAreaPowerDiagram_of_leastAreaGreendlinger
#audit_axioms GroupApproximation.HullSC.hullLemma49KernelPowerStatement_of_leastAreaGreendlinger
