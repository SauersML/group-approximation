import GroupApproximation.GGT.HullSCLemma49EmbeddedArc
import GroupApproximation.GGT.VanKampen.GRegionBoundaryValue
import GroupApproximation.GGT.VanKampen.FaceSetWordHomotopy
import GroupApproximation.GGT.VanKampen.RelativeDiscRealizationPowerCertificate

/-!
# Power-disc boundary adapter

This module connects the source Greendlinger certificate on a planar power
cactus to Hull's cyclic exterior-arc certificate.  The only local equation
needed by Hull's extractor is the value of the selected G-cell face-set
boundary.  `GRegionBoundaryValue` supplies that equation from a cellular
face-pasting cancellation certificate; all boundary, target, and strict
exterior-length fields are copied from the source certificate.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w

private theorem cyclicArc_darts_transport
    {Dart : Type} {cycle cycle' : List Dart} (hcycle : cycle = cycle')
    (arc : Embedded.CyclicArc cycle) :
    ({ start := Fin.cast
        (congrArg (fun c => c.length + 1) hcycle) arc.start
       length := arc.length
       length_le := by simpa [hcycle] using arc.length_le } :
      Embedded.CyclicArc cycle').darts = arc.darts := by
  cases hcycle
  rfl

private theorem targetBoundaryDarts_eq_darts_of_target_eq_none
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta : DiscDiagram.{u, w, 0} W}
    {target : Option (Fin Delta.rCellCount)}
    (arc : Embedded.CyclicArc (Embedded.targetDarts Delta target))
    (htarget : target = none) :
    Embedded.targetBoundaryDarts Delta target arc = arc.darts := by
  cases target with
  | none => rfl
  | some target => simp at htarget

private theorem outerTargetArc_darts_eq_targetBoundaryDarts
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, 0} W}
    {faces : Finset Delta.toCombMap.Face}
    (Gamma : Embedded.Contiguity D eps Delta faces)
    (htarget : Gamma.target = none) :
    (Gamma.outerTargetArc htarget).darts =
      Embedded.targetBoundaryDarts Delta Gamma.target Gamma.targetArc := by
  have hcycle : Embedded.targetDarts Delta Gamma.target =
      Embedded.outerDarts Delta := by
    rw [htarget]
    rfl
  have htransport : (Gamma.outerTargetArc htarget).darts =
      Gamma.targetArc.darts := by
    unfold Embedded.Contiguity.outerTargetArc
    exact cyclicArc_darts_transport hcycle Gamma.targetArc
  have htargetBoundary : Embedded.targetBoundaryDarts Delta Gamma.target
      Gamma.targetArc = Gamma.targetArc.darts := by
    exact targetBoundaryDarts_eq_darts_of_target_eq_none
      (target := Gamma.target) Gamma.targetArc htarget
  rw [htransport, htargetBoundary]

/-- A source certificate with a cellular pasting of its selected G-region
produces the cyclic exterior-arc object used by Hull's Lemma 4.9. -/
theorem lemma49EmbeddedExteriorArc_of_sourceCertificate
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ} {mu : ℝ}
    {Z : HullSC.Lemma49GeodesicPowerDiagram D v g n}
    (hinput : RelWord.IsLemma49Input D
      (RelWord.symmetrized v) eps mu rho)
    (C : Lemma49SourceGreendlingerCertificate D v g n eps mu Z)
    (hmu : 0 ≤ mu)
    (pasting : Embedded.FaceSetWordHomotopy C.diagram C.faces
      C.contiguity.boundary.cycle []) :
    Nonempty (HullSC.Lemma49EmbeddedExteriorArc D v g n eps mu Z) := by
  have htarget : C.contiguity.target = none := C.target_eq
  have hboundary : C.diagram.boundaryWord =
      HullSC.lemma49BoundaryPower Z.boundaryWord n := C.boundaryWord_eq
  have hlarge := C.exterior_large
  have harcs := C.contiguity.arcs_value_of_pasting pasting
  have harcs' :
      GGT.RelLetter.listVal
          (Embedded.dartWord C.diagram C.contiguity.sourceArc.darts) =
        GGT.RelLetter.listVal
            (Embedded.dartWord C.diagram C.contiguity.rightSide) *
          GGT.RelLetter.listVal
            (Embedded.dartWord C.diagram
              (C.contiguity.outerTargetArc htarget).darts) *
          GGT.RelLetter.listVal
            (Embedded.dartWord C.diagram C.contiguity.leftSide) := by
    rw [outerTargetArc_darts_eq_targetBoundaryDarts C.contiguity htarget]
    exact harcs
  exact HullSC.exists_lemma49EmbeddedExteriorArc Z hinput
    C.contiguity htarget hboundary hmu
    hlarge harcs'

/-- A source certificate whose selected region admits a planar face-deletion
schedule produces the same cyclic exterior-arc object. -/
theorem lemma49EmbeddedExteriorArc_of_sourceCertificate_of_peeling
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ} {mu : ℝ}
    {Z : HullSC.Lemma49GeodesicPowerDiagram D v g n}
    (hinput : RelWord.IsLemma49Input D
      (RelWord.symmetrized v) eps mu rho)
    (C : Lemma49SourceGreendlingerCertificate D v g n eps mu Z)
    (hmu : 0 ≤ mu)
    (peeling : Embedded.FaceSetBoundaryPeeling C.contiguity.boundary) :
    Nonempty (HullSC.Lemma49EmbeddedExteriorArc D v g n eps mu Z) := by
  apply lemma49EmbeddedExteriorArc_of_sourceCertificate hinput C hmu
  exact peeling.to_homotopy

end VanKampen
end GGT
end GroupApproximation
