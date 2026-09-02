import GroupApproximation.GGT.VanKampen.FaceSetPeelWitness
import GroupApproximation.GGT.VanKampen.RelativeDiscRealizationPowerAdapter
import GroupApproximation.GGT.VanKampen.ClosedWalkValue

/-!
# The source face-pasting certificate for Hull's Lemma 4.9

This file states the one cellular cancellation certificate needed after
Osin's source Greendlinger selection.  The selected faces are G-cells in the
planar `O`-equivalent diagram, and their boundary cycle must admit a planar
face-deletion schedule.  The schedule theorem turns this certificate into
the face-set homotopy and then into Hull's cyclic exterior arc.
The source is Osin's Appendix Definition M and Lemma 4.9.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The strictly smaller source certificate -/

/-- Every source Greendlinger power certificate pastes its selected G-cell
boundary cycle to the empty word.

This used to ask for a face-deletion schedule.  A schedule is only a proof
device: every consumer takes it through `FaceSetBoundaryPeeling.to_homotopy`
and none inspects it.  Asking for the homotopy directly is strictly weaker, and
it is what a closed-walk argument can supply without an ear, without an
unpinched face and without the erased region having a single boundary cycle. -/
def HullLemma49SourceFacePastingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
      D v g n eps mu Z),
    GGT.VanKampen.Embedded.FaceSetWordHomotopy C.diagram C.faces
      C.contiguity.boundary.cycle []

/-- The planar one-step certificate is exactly the geometric input needed by
the source-face pasting step.  The vk conversion
`faceSetBoundaryPeelWitness_of_planar` supplies the oracle witness, and the
finite face-count induction supplies the complete peeling. -/
theorem hullLemma49SourceFacePastingStatement_of_planar
    (hplanar :
      ∀ {G : Type u} [Group G] {Lambda : Type w}
        {W : Set (List (GGT.RelLetter G Lambda))}
        {Delta : GGT.VanKampen.DiscDiagram.{u, w, 0} W}
        {faces : Finset Delta.toCombMap.Face}
        (boundary : GGT.VanKampen.Embedded.FaceSetBoundary Delta faces),
        GGT.VanKampen.Embedded.PlanarFacePeelCertificate boundary) :
    HullLemma49SourceFacePastingStatement.{u, w} := by
  intro G _ Lambda D v g n eps mu Z C
  have hpeeling : GGT.VanKampen.Embedded.FaceSetBoundaryPeeling
      C.contiguity.boundary := by
    apply GGT.VanKampen.Embedded.faceSetBoundaryPeeling_of_faceSetBoundary_of_oracle
      C.contiguity.boundary
    intro faces boundary
    exact GGT.VanKampen.Embedded.faceSetBoundaryPeelWitness_of_planar boundary
      (hplanar boundary)
  exact hpeeling.to_homotopy

/-- The closed-walk route.  An assembly of every selected boundary cycle from
its own faces discharges the pasting statement, with no ear, no unpinched face
and no single-cycle remainder. -/
theorem hullLemma49SourceFacePastingStatement_of_regionAssembly
    (hassembly : GGT.VanKampen.RegionFaceAssemblyStatement.{u, w, 0}) :
    HullLemma49SourceFacePastingStatement.{u, w} := by
  intro G _ Lambda D v g n eps mu Z C
  exact GGT.VanKampen.faceSetWordHomotopy_of_regionAssembly hassembly
    C.contiguity.boundary

/-- The source face-pasting certificate gives the embedded exterior arc used
by the cyclic correction lemmas. -/
theorem exists_lemma49EmbeddedExteriorArc_of_sourceFacePasting
    (hpasting : HullLemma49SourceFacePastingStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (hinput : RelWord.IsLemma49Input D
      (RelWord.symmetrized v) eps mu rho)
    (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
      D v g n eps mu Z)
    (hmu : 0 ≤ mu) :
    Nonempty (Lemma49EmbeddedExteriorArc D v g n eps mu Z) := by
  exact GGT.VanKampen.lemma49EmbeddedExteriorArc_of_sourceCertificate
    hinput C hmu (hpasting C)

/-! ## Model check -/

/-- In a one-point source group a nontrivial power diagram cannot occur, so
the source face-pasting certificate is vacuous in that model. -/
theorem hullLemma49SourceFacePastingStatement_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    ∀ {v : List (GGT.RelLetter PUnit Lambda)} {g : PUnit} {n eps : ℕ}
      {mu : ℝ} {Z : Lemma49GeodesicPowerDiagram D v g n},
      (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
        D v g n eps mu Z) →
      GGT.VanKampen.Embedded.FaceSetWordHomotopy C.diagram C.faces
        C.contiguity.boundary.cycle [] := by
  intro v g n eps mu Z C
  exact (Z.power_ne_one (Subsingleton.elim _ _)).elim

end HullSC
end GroupApproximation
