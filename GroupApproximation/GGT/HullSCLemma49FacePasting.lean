import GroupApproximation.GGT.VanKampen.RelativeDiscRealizationPowerAdapter

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

/-- Every source Greendlinger power certificate has a face-deletion schedule
from its selected G-cell boundary.  This is the precise topological input
needed to build the cellular homotopy. -/
def HullLemma49SourceFacePastingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
      D v g n eps mu Z),
    Nonempty (GGT.VanKampen.Embedded.FaceSetBoundaryPeeling
      C.contiguity.boundary)

/-- The vk peeling callback is exactly the certificate needed by the source-face
pasting step.  Keeping this adapter at the certificate boundary lets the
relative disc realization supply the callback without exposing its schedule
construction here. -/
theorem hullLemma49SourceFacePastingStatement_of_faceSetBoundaryPeeling
    (hpeeling :
      ∀ {G : Type u} [Group G] {Lambda : Type w}
        {W : Set (List (GGT.RelLetter G Lambda))}
        {Delta : GGT.VanKampen.DiscDiagram.{u, w, 0} W}
        {faces : Finset Delta.toCombMap.Face}
        (boundary : GGT.VanKampen.Embedded.FaceSetBoundary Delta faces),
        GGT.VanKampen.Embedded.FaceSetBoundaryPeeling boundary) :
    HullLemma49SourceFacePastingStatement.{u, w} := by
  intro G _ Lambda D v g n eps mu Z C
  exact ⟨hpeeling C.contiguity.boundary⟩

/-- The currently landed vk theorem has an explicit one-step oracle.  This
bridge keeps that oracle visible and applies
`faceSetBoundaryPeeling_of_faceSetBoundary` at the selected certificate. -/
theorem hullLemma49SourceFacePastingStatement_of_vkFaceSetBoundaryPeeling
    (horacle :
      ∀ {G : Type u} [Group G] {Lambda : Type w}
        {W : Set (List (GGT.RelLetter G Lambda))}
        {Delta : GGT.VanKampen.DiscDiagram.{u, w, 0} W},
        GGT.VanKampen.Embedded.FaceSetBoundaryPeelOracle
          (Delta := Delta)) :
    HullLemma49SourceFacePastingStatement.{u, w} := by
  intro G _ Lambda D v g n eps mu Z C
  exact ⟨GGT.VanKampen.Embedded.faceSetBoundaryPeeling_of_faceSetBoundary
    C.contiguity.boundary (horacle (Delta := C.diagram))⟩

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
  obtain ⟨peeling⟩ := hpasting C
  exact GGT.VanKampen.lemma49EmbeddedExteriorArc_of_sourceCertificate_of_peeling
    hinput C hmu peeling

/-! ## Model check -/

/-- In a one-point source group a nontrivial power diagram cannot occur, so
the source face-pasting certificate is vacuous in that model. -/
theorem hullLemma49SourceFacePastingStatement_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    ∀ {v : List (GGT.RelLetter PUnit Lambda)} {g : PUnit} {n eps : ℕ}
      {mu : ℝ} {Z : Lemma49GeodesicPowerDiagram D v g n},
      (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
        D v g n eps mu Z) →
      Nonempty (GGT.VanKampen.Embedded.FaceSetBoundaryPeeling
        C.contiguity.boundary) := by
  intro v g n eps mu Z C
  exact (Z.power_ne_one (Subsingleton.elim _ _)).elim

end HullSC
end GroupApproximation
