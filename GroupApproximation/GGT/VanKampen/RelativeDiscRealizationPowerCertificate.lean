import GroupApproximation.GGT.VanKampen.RelativeDiscRealizationPower
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

/-!
# Source Greendlinger certificates for geodesic power cacti

This file applies Osin's source-faithful quasi-geodesic Greendlinger theorem
to the explicit power cactus.  The output retains the `O`-equivalent diagram,
the embedded exterior region, the literal repeated boundary word, and the
strict `1 - 13 * mu` exterior estimate.

The former Hull-specific `Lemma49GreendlingerCertificate` interface is not in
the current library.  `Lemma49SourceGreendlingerCertificate` is the live
embedded certificate: `HullSCLemma49EmbeddedArc` converts such an embedded
region to its cyclic word data once the G-region boundary-value equation is
supplied.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC

universe u w

/-- The result of applying source Gr0 to the explicit power realization. -/
structure Lemma49SourceGreendlingerCertificate
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (v : List (GGT.RelLetter G Lambda)) (g : G) (n eps : ℕ) (mu : ℝ)
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) where
  realization : RelativeDiscRealizationPower D v g n Z
  diagram : DiscDiagram.{u, w, 0} (RelWord.symmetrized v)
  equivalent : Nonempty
    (OEquivalentDiscDiagram realization.diagram diagram)
  boundaryWord_eq : diagram.boundaryWord =
    lemma49BoundaryPower Z.boundaryWord n
  faces : Finset diagram.toCombMap.Face
  contiguity : Embedded.Contiguity D eps diagram faces
  target_eq : contiguity.target = none
  exterior_large :
    (1 - 13 * mu) *
        ((Embedded.cell diagram contiguity.source).word.length : ℝ) <
      (contiguity.sourceArc.length : ℝ)

namespace Lemma49SourceGreendlingerCertificate

/-- Compose the cactus cell index with the `O`-equivalence cell index. -/
noncomputable def cellIndex
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : HullSC.Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49SourceGreendlingerCertificate D v g n eps mu Z) :
    Fin Z.cells.length ≃ Fin C.diagram.rCellCount :=
  C.realization.cellIndex.trans (Classical.choice C.equivalent).cellIndex

/-- The final `O`-equivalent cell at the composed algebraic index reads the
original oriented relator word. -/
theorem cellWord_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : HullSC.Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49SourceGreendlingerCertificate D v g n eps mu Z)
    (i : Fin Z.cells.length) :
    (Embedded.cell C.diagram (C.cellIndex i)).word =
      (Z.cells.get i).relator := by
  let E := Classical.choice C.equivalent
  calc
    (Embedded.cell C.diagram (C.cellIndex i)).word =
        (Embedded.cell C.realization.diagram
          (C.realization.cellIndex i)).word := by
      exact E.cellWord_eq (C.realization.cellIndex i)
    _ = (Z.cells.get i).relator := C.realization.cellWord_eq i

end Lemma49SourceGreendlingerCertificate

/-- The explicit power cactus has a positive number of relator cells. -/
theorem relativeDiscRealizationPower_rCellCount_pos
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n) :
    0 < (relativeDiscRealizationPower D Z).diagram.rCellCount := by
  change 0 < Z.cactusRelatorCells.length
  rw [HullSC.Lemma49GeodesicPowerDiagram.cactusRelatorCells,
    List.length_ofFn]
  have hcells : Z.cells.length = Z.factors.length := by
    have hlength := congrArg List.length Z.cell_values
    simpa only [List.length_map] using hlength
  rw [hcells, Z.factors_length]
  exact Z.area_pos

/-- Applying source-faithful relative Greendlinger to the planar power cactus
produces the live embedded Hull 4.9 certificate.  The quasi-geodesic premise
is stated separately because Hull's long-period and stable-translation
branches prove it with different constants. -/
theorem lemma49Certificate_of_relativeGreendlinger
    (hgeom : RelativeGreendlingerQuasiGeodesicStatement.{u, w, 0})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lambda c mu : ℝ)
    (hlambda : 0 < lambda) (hlambdaUpper : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho : ℕ, 0 < rho ∧
      ∀ (v : List (GGT.RelLetter G Lambda)) (g : G) (n : ℕ)
        (Z : HullSC.Lemma49GeodesicPowerDiagram D v g n),
        OsinCCondition D (RelWord.symmetrized v) eps mu lambda c rho →
        IsLambdaCQuasiGeodesicWord D lambda c
          (lemma49BoundaryPower Z.boundaryWord n) →
        Nonempty
          (Lemma49SourceGreendlingerCertificate D v g n eps mu Z) := by
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    hgeom D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro v g n Z hcondition hboundary
  let realization := relativeDiscRealizationPower D Z
  have hboundary' : IsLambdaCQuasiGeodesicWord D lambda c
      realization.diagram.boundaryWord := by
    rw [realization.outerWord_eq]
    exact hboundary
  have hcells : 0 < realization.diagram.rCellCount := by
    exact relativeDiscRealizationPower_rCellCount_pos D Z
  obtain ⟨diagram, hequivalent, faces, contiguity, htarget, hlarge⟩ :=
    hgood (RelWord.symmetrized v) hcondition realization.diagram
      realization.reduced hcells hboundary'
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
end GroupApproximation
