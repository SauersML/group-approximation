import GroupApproximation.GGT.VanKampen.RelativeDiscRealization
import GroupApproximation.GGT.VanKampen.GeodesicQuasiGeodesic
import GroupApproximation.GGT.VanKampen.Estimating.Assembly

/-!
# Realized relative Greendlinger witnesses

The corrected estimating theorem is stated for a planar disc whose outer word
is a quasi-geodesic relative word.  The algebraic Hull input instead supplies a
`RelativeReducedDiagram`.  This file proves the transport step through the vk
realization interface: a realization has the same relator-cell count and its
outer word is the designated boundary word with base letters, so the corrected
quasi-geodesic theorem applies directly.

The result deliberately stops at the planar exterior witness.  Converting its
dart arcs into the abstract `RelativeDiagramCertificate` is the separate vk
certificate theorem; no consumer of this module needs to inspect a dart.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.VanKampen

universe u w

/-- A vk realization transports positivity of the algebraic relator-cell list
to positivity of the planar relator-cell count. -/
theorem RelativeDiscRealization.rCellCount_pos
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {D : GGT.RelGenSet G Lambda}
    {Z : RelativeReducedDiagram D W R}
    (C : RelativeDiscRealization D W Z) : 0 < C.diagram.rCellCount := by
  have hcount : C.diagram.rCellCount = Z.cells.length := by
    have hcard := Fintype.card_congr C.cellIndex
    simpa only [Fintype.card_fin] using hcard.symm
  rw [hcount, Z.cells_length]
  exact Z.area_pos

/-- A realized boundary inherits a quasi-geodesic hypothesis from the
algebraic designated boundary word. -/
theorem RelativeDiscRealization.boundary_quasiGeodesic
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {D : GGT.RelGenSet G Lambda}
    {Z : RelativeReducedDiagram D W R}
    {lambda c : ℝ}
    (C : RelativeDiscRealization D W Z)
    (hboundary : IsLambdaCQuasiGeodesicWord D lambda c
      (Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))) :
    IsLambdaCQuasiGeodesicWord D lambda c C.diagram.boundaryWord := by
  rw [C.outerWord_eq]
  exact hboundary

/-! ## Corrected est applied through vk realization -/

/-- Corrected Osin Greendlinger, transported through the vk realization
statement.  The output is a planar `O`-equivalent diagram and an exterior
contiguity witness for every algebraic reduced diagram whose base-letter
boundary is quasi-geodesic. -/
theorem exists_realized_relativeGreendlingerWitness
    (hgeom : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{u, w, 0})
    (hreal : GGT.VanKampen.RelativeDiscRealizationStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    {lambda c mu : ℝ}
    (hlambda : 0 < lambda) (hlambdaUpper : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho : ℕ, 0 < rho ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda))),
        GGT.VanKampen.OsinCCondition D W eps mu lambda c rho →
          ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
            IsLambdaCQuasiGeodesicWord D lambda c
              (Z.boundaryWord.map
                (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) →
              ∃ (C : RelativeDiscRealization D W Z)
                (Delta' : DiscDiagram.{u, w, 0} W),
                Nonempty (GGT.VanKampen.OEquivalentDiscDiagram C.diagram Delta') ∧
                  ∃ (faces : Finset Delta'.toCombMap.Face)
                    (Gamma : GGT.VanKampen.Embedded.Contiguity
                      D eps Delta' faces),
                    Gamma.target = none ∧
                      (1 - 13 * mu) *
                          ((GGT.VanKampen.Embedded.cell Delta'
                            Gamma.source).word.length : ℝ) <
                        (Gamma.sourceArc.length : ℝ) := by
  obtain ⟨eps, rho, hrho, hgood⟩ := hgeom D hhyper lambda c mu
    hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro W hcondition R Z hboundary
  obtain ⟨C⟩ := hreal D W R Z
  have hred : C.diagram.Reduced := C.reduced
  have hcells : 0 < C.diagram.rCellCount :=
    RelativeDiscRealization.rCellCount_pos C
  have hboundary' : IsLambdaCQuasiGeodesicWord D lambda c
      C.diagram.boundaryWord :=
    RelativeDiscRealization.boundary_quasiGeodesic C hboundary
  obtain ⟨Delta', hequiv, faces, Gamma, htarget, hlarge⟩ :=
    hgood W hcondition C.diagram hred hcells hboundary'
  exact ⟨C, Delta', hequiv, faces, Gamma, htarget, hlarge⟩

/-- The three est construction components and the vk realization statement
produce the realized corrected Greendlinger witness.  This is the source-level
interface used before the exterior witness is converted into a relative
certificate. -/
theorem exists_realized_relativeGreendlingerWitness_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundConstructionStatement.{u, w, 0})
    (hreal : GGT.VanKampen.RelativeDiscRealizationStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    {lambda c mu : ℝ}
    (hlambda : 0 < lambda) (hlambdaUpper : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho : ℕ, 0 < rho ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda))),
        GGT.VanKampen.OsinCCondition D W eps mu lambda c rho →
          ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
            IsLambdaCQuasiGeodesicWord D lambda c
              (Z.boundaryWord.map
                (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) →
              ∃ (C : RelativeDiscRealization D W Z)
                (Delta' : DiscDiagram.{u, w, 0} W),
                Nonempty (GGT.VanKampen.OEquivalentDiscDiagram C.diagram Delta') ∧
                  ∃ (faces : Finset Delta'.toCombMap.Face)
                    (Gamma : GGT.VanKampen.Embedded.Contiguity
                      D eps Delta' faces),
                    Gamma.target = none ∧
                      (1 - 13 * mu) *
                          ((GGT.VanKampen.Embedded.cell Delta'
                            Gamma.source).word.length : ℝ) <
                        (Gamma.sourceArc.length : ℝ) := by
  exact exists_realized_relativeGreendlingerWitness
    (GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_components
      hselection hpieces hunbound)
    hreal D hhyper hlambda hlambdaUpper hc hmu hmuUpper

/-- The geodesic-boundary form uses est's relative geodesic-to-quasi-geodesic
lemma before invoking the realized corrected Greendlinger witness. -/
theorem exists_realized_relativeGreendlingerWitness_of_geodesicBoundary
    (hgeom : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{u, w, 0})
    (hreal : GGT.VanKampen.RelativeDiscRealizationStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    {lambda c mu : ℝ}
    (hlambda : 0 < lambda) (hlambdaUpper : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho : ℕ, 0 < rho ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda))),
        GGT.VanKampen.OsinCCondition D W eps mu lambda c rho →
          ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
            GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary
              (Z.boundaryWord.map
                (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) →
              ∃ (C : RelativeDiscRealization D W Z)
                (Delta' : DiscDiagram.{u, w, 0} W),
                Nonempty (GGT.VanKampen.OEquivalentDiscDiagram C.diagram Delta') := by
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    exists_realized_relativeGreendlingerWitness hgeom hreal D hhyper
      hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro W hcondition R Z hgeo
  have hqg : IsLambdaCQuasiGeodesicWord D lambda c
      (Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) :=
    isLambdaCQuasiGeodesicWord_of_isGeodesicWord D hgeo
      hlambdaUpper hc
  obtain ⟨C, Delta', hequiv, _⟩ := hgood W hcondition R Z hqg
  exact ⟨C, Delta', hequiv⟩

/-! ## Boundary-contiguity packaging -/

/-- The corrected theorem's exterior witness packages directly as the
boundary-contiguity object exposed to a certificate adapter.  The package
retains the relator-cell index and the outer-target equation while keeping
the planar darts below this interface. -/
theorem exists_realized_embeddedBoundaryContiguity_of_geodesicBoundary
    (hgeom : GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement.{u, w, 0})
    (hreal : GGT.VanKampen.RelativeDiscRealizationStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    {lambda c mu : ℝ}
    (hlambda : 0 < lambda) (hlambdaUpper : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho : ℕ, 0 < rho ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda))),
        GGT.VanKampen.OsinCCondition D W eps mu lambda c rho →
          ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
            GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary
              (Z.boundaryWord.map
                (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) →
              ∃ (C : RelativeDiscRealization D W Z)
                (Delta' : DiscDiagram.{u, w, 0} W)
                (i : Fin Delta'.rCellCount)
                (Gamma : EmbeddedBoundaryContiguity D eps Delta' i),
                Nonempty (GGT.VanKampen.OEquivalentDiscDiagram C.diagram Delta') ∧
                  Gamma.region.source = i ∧
                  Gamma.region.target = none ∧
                  (1 - 13 * mu) *
                      ((GGT.VanKampen.Embedded.cell Delta' i).word.length : ℝ) <
                    (Gamma.region.sourceArc.length : ℝ) := by
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    exists_realized_relativeGreendlingerWitness hgeom hreal D hhyper
      hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro W hcondition R Z hgeo
  have hqg : IsLambdaCQuasiGeodesicWord D lambda c
      (Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) :=
    isLambdaCQuasiGeodesicWord_of_isGeodesicWord D hgeo
      hlambdaUpper hc
  obtain ⟨C, Delta', hequiv, faces, Gamma, htarget, hlarge⟩ :=
    hgood W hcondition R Z hqg
  let packaged : EmbeddedBoundaryContiguity D eps Delta' Gamma.source := {
    faces := faces
    region := Gamma
    source_eq := rfl
    target_eq := htarget }
  exact ⟨C, Delta', Gamma.source, packaged, hequiv, rfl, htarget, hlarge⟩

/-- The source-level boundary package uses exactly the three est construction
components and the vk realization statement.  This is the input shape for
the later conversion from embedded boundary data to a relative certificate. -/
theorem exists_realized_embeddedBoundaryContiguity_of_components_and_geodesicBoundary
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundConstructionStatement.{u, w, 0})
    (hreal : GGT.VanKampen.RelativeDiscRealizationStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    {lambda c mu : ℝ}
    (hlambda : 0 < lambda) (hlambdaUpper : lambda ≤ 1)
    (hc : 0 ≤ c) (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16) :
    ∃ eps rho : ℕ, 0 < rho ∧
      ∀ (W : Set (List (GGT.RelLetter G Lambda))),
        GGT.VanKampen.OsinCCondition D W eps mu lambda c rho →
          ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
            GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary
              (Z.boundaryWord.map
                (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) →
              ∃ (C : RelativeDiscRealization D W Z)
                (Delta' : DiscDiagram.{u, w, 0} W)
                (i : Fin Delta'.rCellCount)
                (Gamma : EmbeddedBoundaryContiguity D eps Delta' i),
                Nonempty (GGT.VanKampen.OEquivalentDiscDiagram C.diagram Delta') ∧
                  Gamma.region.source = i ∧
                  Gamma.region.target = none ∧
                  (1 - 13 * mu) *
                      ((GGT.VanKampen.Embedded.cell Delta' i).word.length : ℝ) <
                    (Gamma.region.sourceArc.length : ℝ) := by
  exact exists_realized_embeddedBoundaryContiguity_of_geodesicBoundary
    (GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_components
      hselection hpieces hunbound)
    hreal D hhyper hlambda hlambdaUpper hc hmu hmuUpper

end HullSC
end GroupApproximation
