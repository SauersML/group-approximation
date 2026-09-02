import GroupApproximation.GGT.HullSCRelativeGreendlingerGeodesicConsumers
import GroupApproximation.GGT.HullSCLemma49Assemble

/-!
# Hull's Lemma 4.9 power-diagram leaf from named inputs

`HullSC.HullLemma49ShortestGeodesicPowerDiagramStatement` is the assembly leaf
`hullLemma49GeodesicPowerDiagram`.  This module reduces it to five named
propositions and nothing else.

Two of its former inputs have gone.  `HullLemma49SourceFacePastingStatement`
is now proved outright as `hullLemma49SourceFacePastingStatement_holds`, so
`hullLemma49ShortestGeodesicPowerDiagram_of_estimating_components` already
takes only est's three construction propositions and the injectivity callback.
And the callback no longer needs the unrestricted relative Greendlinger
statement: it spends it only through
`exists_relativeBallInjectivityParameters_of_greendlinger`, at diagrams that
are Hull Lemma 4.4 diagrams, so the geodesic-length restricted statement of
`HullSCRelativeGreendlingerSpelling` suffices.

What remains is exactly est's three propositions together with the two
lane-named residues of the estimating-to-certificate route, the vk realization
at a supplied admissible spelling and the one-cell exterior-arc conversion.

Every declaration below is a complete proof; no placeholder of any kind is
introduced here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The injectivity callback at the restricted statement -/

/-- **The Lemma 4.9 injectivity callback from the geodesic-length statement.**
This mirrors `hullLemma49InjectivityCallback_of_relativeGreendlinger`, with the
weaker hypothesis.  It is sound because the callback spends its input only
through relative-ball injectivity, whose diagrams carry
`boundaryWord_geodesic`. -/
theorem hullLemma49InjectivityCallback_of_geodesicLengthGreendlinger
    (hgeom : RelativeGreendlingerGeodesicLengthStatement.{u, w}) :
    HullLemma49InjectivityCallback.{u, w} := by
  intro G _ Lambda D hD delta _hdelta
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    exists_relativeBallInjectivityParameters_of_geodesicLengthGreendlinger
      hgeom D hD (8 * delta + 1)
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hker
  exact hgood W q hinput.toIsLemma44Input hker

/-! ## The composite -/

/-- **Hull's Lemma 4.9 power-diagram leaf, from five named inputs.**

The three estimating construction propositions are est's; the realization at a
supplied admissible spelling and the one-cell exterior-arc conversion are the
two residues of `HullSCRelativeGreendlingerSpelling`.  No boundary hypothesis
about an arbitrary reduced diagram appears, and neither does
`AllReducedDiagramsHaveBaseGeodesicBoundary`. -/
theorem hullLemma49ShortestGeodesicPowerDiagramStatement_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{0, 0, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0})
    (hreal : RelativeDiscRealizationSpellingStatement.{0, 0})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{0, 0}) :
    HullLemma49ShortestGeodesicPowerDiagramStatement.{0, 0} :=
  hullLemma49ShortestGeodesicPowerDiagram_of_estimating_components
    hselection hpieces hunbound
    (hullLemma49InjectivityCallback_of_geodesicLengthGreendlinger
      (relativeGreendlingerGeodesicLengthStatement_of_components
        hselection hpieces hunbound hreal hconv))

/-- The kernel-power form of Hull's Lemma 4.9, from the same five inputs. -/
theorem hullLemma49KernelPowerStatement_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{0, 0, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0})
    (hreal : RelativeDiscRealizationSpellingStatement.{0, 0})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{0, 0}) :
    HullLemma49KernelPowerStatement.{0, 0} :=
  hullLemma49KernelPowerStatement_of_geodesicPowerDiagram
    (hullLemma49ShortestGeodesicPowerDiagramStatement_of_components
      hselection hpieces hunbound hreal hconv)

/-! ## The composite with the realization discharged -/

/-- **Hull's Lemma 4.9 power-diagram leaf, from four named inputs.**

`RelativeDiscRealizationSpellingStatement` is no longer a hypothesis: it is
proved, as `relativeDiscRealizationSpellingStatement`, from the cactus
parameterized by the outer spelling.  So the leaf now rests on est's three
construction propositions and the one-cell exterior-arc conversion. -/
theorem hullLemma49ShortestGeodesicPowerDiagramStatement_of_estimating
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{0, 0, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{0, 0}) :
    HullLemma49ShortestGeodesicPowerDiagramStatement.{0, 0} :=
  hullLemma49ShortestGeodesicPowerDiagramStatement_of_components
    hselection hpieces hunbound relativeDiscRealizationSpellingStatement hconv

/-- The kernel-power form, from the same four inputs. -/
theorem hullLemma49KernelPowerStatement_of_estimating
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{0, 0, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{0, 0, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{0, 0, 0})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{0, 0}) :
    HullLemma49KernelPowerStatement.{0, 0} :=
  hullLemma49KernelPowerStatement_of_components
    hselection hpieces hunbound relativeDiscRealizationSpellingStatement hconv

/-- Relative-ball injectivity, the Lemma 4.4 side, from the same four. -/
theorem exists_relativeBallInjectivityParameters_of_estimating
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{u, w, 0})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (R : ℕ) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda)))
        {Q : Type*} [Group Q] (q : G →* Q),
        RelWord.IsLemma44Input D W eps mu rho →
        q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
          Set.InjOn q (cayleyBall D.alphabet R) :=
  exists_relativeBallInjectivityParameters_of_components
    hselection hpieces hunbound relativeDiscRealizationSpellingStatement hconv
    D hemb R


end HullSC
end GroupApproximation
