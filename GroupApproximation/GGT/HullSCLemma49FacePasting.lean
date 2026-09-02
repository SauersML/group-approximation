import GroupApproximation.GGT.VanKampen.RelativeDiscRealizationPowerAdapter

/-!
# The source face-pasting certificate for Hull's Lemma 4.9

This file states the one cellular cancellation certificate needed after
Osin's source Greendlinger selection.  The selected faces are G-cells in the
planar `O`-equivalent diagram, and their boundary cycle must reduce to the
empty dart word by complete face deletions and inverse dart-pair deletions.
The adapter theorem turns this certificate into Hull's cyclic exterior arc.
The source is Osin's Appendix Definition M and Lemma 4.9.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The strictly smaller source certificate -/

/-- Every source Greendlinger power certificate has a cellular homotopy from
the selected G-cell boundary to the empty dart word. -/
def HullLemma49SourceFacePastingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
      D v g n eps mu Z),
    Nonempty (GGT.VanKampen.Embedded.FaceSetWordHomotopy
      C.diagram C.faces C.contiguity.boundary.cycle [])

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
  obtain ⟨pasting⟩ := hpasting C
  exact GGT.VanKampen.lemma49EmbeddedExteriorArc_of_sourceCertificate
    hinput C hmu pasting

/-! ## Model check -/

/-- In a one-point source group a nontrivial power diagram cannot occur, so
the source face-pasting certificate is vacuous in that model. -/
theorem hullLemma49SourceFacePastingStatement_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    ∀ {v : List (GGT.RelLetter PUnit Lambda)} {g : PUnit} {n eps : ℕ}
      {mu : ℝ} {Z : Lemma49GeodesicPowerDiagram D v g n},
      (C : GGT.VanKampen.Lemma49SourceGreendlingerCertificate
        D v g n eps mu Z) →
      Nonempty (GGT.VanKampen.Embedded.FaceSetWordHomotopy
        C.diagram C.faces C.contiguity.boundary.cycle []) := by
  intro v g n eps mu Z C
  exact (Z.power_ne_one (Subsingleton.elim _ _)).elim

end HullSC
end GroupApproximation
