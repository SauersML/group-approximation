import GroupApproximation.GGT.HullSCLeastAreaGreendlingerTwins
import GroupApproximation.GGT.HullSCLemma44BoundedBridge
import GroupApproximation.GGT.HullSCLemma51EmbeddedBridge
import GroupApproximation.GGT.DGOProposition414General
import GroupApproximation.GGT.DGOLemma421FromUniform414
import GroupApproximation.GGT.HullYiCyclicProductClosure
import GroupApproximation.GGT.HullYiFiniteFamilyInduction
import GroupApproximation.GGT.HullSCFillingSelectionTheorem316
import GroupApproximation.GGT.HullSCAuxiliaryRelatorPublished
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's Theorem 7.1 at one target, over the least-area leaves

The canonical selected-family Lemma 4.4 over strongly bounded families, with the
certificate asked only at least-area diagrams, and the one-target form of Hull's
Theorem 7.1 assembled from:

* `GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement`, Osin's
  Lemma 4.4 at least-area diagrams (through the least-area spelling waist and the
  least-area Lemma 4.9 chain of `HullSCLeastAreaGreendlingerTwins`);
* `RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement`, Osin's Lemma 5.1
  in the embedded form, or its producer `BoundedRelativeLinearAreaTransferStatement`
  (`relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_boundedTransfer`).

`boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea` is
`boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesic` with the
least-area certificate family; every numerical choice is the original's.  The
selection and Corollary 5.7 inputs are closed.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- **Hull Lemma 4.4, canonical bounded form, from the least-area certificate and
the embedded bridge.**  The certificate family is asked only at least-area
diagrams with a quasi-geodesic spelling, which is what the least-area Greendlinger
waist provides and what the embedded bridge consumes. -/
theorem boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea
    (hgeom : RelativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement.{u, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{u, u, 0}) :
    BoundedHullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S D R
  let mu : ℝ := 1 / 1000
  have hmuPos : 0 < mu := by
    dsimp [mu]
    norm_num
  have hmuSixteen : mu ≤ 1 / 16 := by
    dsimp [mu]
    norm_num
  have hmuNinetyTwo : mu ≤ 1 / 92 := by
    dsimp [mu]
    norm_num
  have hmuThousand : mu ≤ 1 / 1000 := le_rfl
  obtain ⟨eps, rho₀, hcertificate⟩ :=
    hgeom D.rel D.embedded mu hmuPos hmuSixteen
  let fullRadius : ℕ := max R 1
  let boundaryScale : ℕ := 2 * fullRadius + 2 * eps + 1
  let rho : ℕ := max rho₀ (max (8 * boundaryScale) (20 * (eps + 1)))
  have hrho₀ : rho₀ ≤ rho := Nat.le_max_left _ _
  have hrhoScale : 8 * boundaryScale ≤ rho :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hrhoDehn : 20 * (eps + 1) ≤ rho :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hscalePos : (0 : ℝ) < (boundaryScale : ℝ) := by
    dsimp [boundaryScale, fullRadius]
    positivity
  have hrhoScaleReal :
      (8 : ℝ) * (boundaryScale : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrhoScale
  have hthreshold :
      4 * ((2 * max R 1 + 2 * eps + 1 : ℕ) : ℝ) <
        (3 / 4 : ℝ) * (rho : ℝ) := by
    change 4 * (boundaryScale : ℝ) < (3 / 4 : ℝ) * (rho : ℝ)
    nlinarith
  refine ⟨eps, rho, mu, hmuPos, ?_⟩
  intro W Q _ q hsc hsurj hker
  have hcert : ∀ (r : ℕ) (Z : RelativeLeastAreaDiagram D.rel W r),
      Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling →
        Nonempty (RelativeDiagramCertificate D.rel W eps mu Z.toRelativeReducedDiagram) :=
    fun r Z hZ => hcertificate rho hrho₀ W r hsc.toIsLemma44Input Z hZ
  have hAlphabet : A.alphabet.carrier ⊆ D.rel.alphabet.carrier := by
    intro x hx
    exact Set.mem_union_left _ (D.base_le hx)
  have hinject :=
    injOn_ball_and_peripheralUnion_of_quasiGeodesicLeastAreaCertificates
      D.rel A.alphabet hAlphabet hsc.toIsLemma44Input hmuNinetyTwo hthreshold
        q hker (hcert (max R 1))
  have hinjectCores : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G)) := by
    intro x hx y hy hxy
    apply hinject.2
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [D.fam_eq i]
      exact hi
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rw [D.fam_eq i]
      exact hi
    · exact hxy
  refine ⟨hinject.1, ?_⟩
  exact quotientPeripheralPreservation_of_embeddedBridge hbridge D q hsurj
    hmuPos hmuThousand hrhoDehn hsc hker hcert hinjectCores

/-- **Hull's Corollary 5.7 in its all-`m` form, closed**, as in the selection
input of the canonical quotient. -/
theorem yiSuitableFiniteFamily_closed : YiSuitableFiniteFamily.{0} :=
  yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr
    (yiSuitablePairAvoidingFiniteOneSided_of_dgoLemma421b
      (GGT.OsinComponents.dgoLemma421b_of_uniform414
        GGT.OsinComponents.dgoProposition414Uniform))

/-- **The torsion-free canonical filling quotient from the least-area leaves**:
the bounded canonical Lemma 4.4 above, the least-area Lemma 4.9 kernel-power
correction, and the closed simultaneous peripheral selection. -/
theorem torsionFreeHullCanonicalQuotientStatement_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    TorsionFreeHullCanonicalQuotientStatement.{0} :=
  torsionFreeHullCanonicalQuotientStatement_of_boundedLemma44_of_lemma49
    (simultaneousAuxiliaryPeripheralSelection_of_finiteYi_theorem316
      yiSuitableFiniteFamily_closed)
    (boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea
      (relativeGreendlingerQuasiGeodesicSpellingLeastAreaStatement_of_leastAreaGreendlinger
        hgreendlinger relativeDiscRealizationSpellingStatement
        relativeExteriorArcConversionAtWordRotatedStatement)
      hbridge)
    (hullLemma49KernelPowerStatement_of_leastAreaGreendlinger hgreendlinger)

/-- **Hull's Theorem 7.1 at one target, from the least-area Greendlinger waist
and the embedded bridge.** -/
theorem hullOneStepStatement_of_leastAreaLeaves
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (hbridge : RelativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement.{0, 0, 0}) :
    HullOneStepStatement.{0} :=
  AuxiliaryPeripheralFamily.hullOneStep_of_canonicalQuotient
    (torsionFreeHullCanonicalQuotientStatement_of_leastAreaLeaves hgreendlinger hbridge)

/-- **Hull's Theorem 7.1 at one target, from the least-area Greendlinger waist
and the bounded linear-area transfer**, the producer of the embedded bridge. -/
theorem hullOneStepStatement_of_leastAreaGreendlinger_of_boundedTransfer
    (hgreendlinger :
      GGT.VanKampen.RelativeGreendlingerQuasiGeodesicLeastAreaStatement.{0, 0, 0})
    (htransfer : BoundedRelativeLinearAreaTransferStatement.{0, 0, 0}) :
    HullOneStepStatement.{0} :=
  hullOneStepStatement_of_leastAreaLeaves hgreendlinger
    (relativeIsoperimetricBridgeQuasiGeodesicEmbeddedStatement_of_boundedTransfer htransfer)

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.boundedHullLemma44CanonicalQuotientStatement_of_quasiGeodesicLeastArea
#audit_closed_axioms GroupApproximation.HullSC.yiSuitableFiniteFamily_closed
#audit_axioms GroupApproximation.HullSC.torsionFreeHullCanonicalQuotientStatement_of_leastAreaLeaves
#audit_axioms GroupApproximation.HullSC.hullOneStepStatement_of_leastAreaLeaves
#audit_axioms GroupApproximation.HullSC.hullOneStepStatement_of_leastAreaGreendlinger_of_boundedTransfer
