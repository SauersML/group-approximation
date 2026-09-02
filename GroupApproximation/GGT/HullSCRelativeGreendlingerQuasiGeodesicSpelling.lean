import GroupApproximation.GGT.HullSCRelativeGreendlingerSpelling
import GroupApproximation.GGT.HullSCLemma49FromRelativeGreendlinger

/-!
# Relative Greendlinger at the weakest boundary hypothesis its proof uses

`HullSCRelativeGreendlingerSpelling` proves
`RelativeGreendlingerGeodesicLengthStatement`, whose boundary hypothesis asks
the designated boundary word to be **geodesic** in the relative alphabet.  That
serves the Hull Lemma 4.4 injectivity consumers, where the diagram is a
`Lemma44OrientedRelatorDiagram` and geodesicity is the discarded
`boundaryWord_geodesic` field.

**It does not serve Hull's Lemma 4.9.**
`Lemma49GeodesicPowerDiagram.toRelativeReducedDiagram`
(`GGT/HullSCLemma49FromRelativeGreendlinger.lean:33`) sets

* `boundaryWord := (lemma49BoundaryPower Z.boundaryWord n).map GGT.RelLetter.val`
* `boundary := g ^ n`

and `lemma49BoundaryPower w n` is `w` repeated `n` times
(`GGT/HullSCLemma49PowerDiagram.lean:297`).  So the geodesic clause would read
`n * Z.boundaryWord.length = wordNorm D.alphabet.carrier (g ^ n)`, and
`wordNorm (g ^ n) ≤ n * wordNorm g` is an inequality, strict as soon as `g`
fails to be translation-like.  The power boundary is quasi-geodesic, not
geodesic, and Hull's Lemma 4.9 splits into cases exactly on the translation
gap that makes it so.

This module therefore states the hypothesis at the weakest form the proof
actually consumes.  Reading the reduction in
`relativeGreendlingerGeodesicLengthStatement_of_components`, the geodesic
clause is used only to manufacture an admissible spelling of the boundary word
that is `(1/4, 1)`-quasi-geodesic — the parameters
`RelWord.IsLemma44Input.toOsinCCondition` supplies.  Asking for that spelling
directly is strictly weaker and serves both chains:

* geodesic boundary words satisfy it
  (`hasQuasiGeodesicSpelling_of_hasGeodesicBoundaryLength`), so the Lemma 4.4
  injectivity flip is unaffected;
* a power boundary word can satisfy it too, which the geodesic clause makes
  impossible — supplying it there is Hull's translation-gap case analysis and
  is named, not proved, here.

Every declaration below is a complete proof or a named proposition; no
placeholder of any kind is introduced here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.VanKampen

universe u w

/-! ## The boundary hypothesis the reduction actually consumes -/

/-- **The designated boundary word has an admissible `(1/4, 1)`-quasi-geodesic
relative spelling.**  The spelling is letterwise, so arcs of the relative word
and of the `List G` boundary word correspond; its value is the designated
boundary element.  No geodesicity and no membership in `D.base` is asked. -/
def RelativeReducedDiagram.HasQuasiGeodesicSpelling
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R) : Prop :=
  ∃ outer : List (GGT.RelLetter G Lambda),
    outer.map GGT.RelLetter.val = Z.boundaryWord ∧
      GGT.RelLetter.listVal outer = Z.boundary ∧
        IsLambdaCQuasiGeodesicWord D (1 / 4) 1 outer

/-- **A geodesic designated boundary has such a spelling.**  So the Lemma 4.4
injectivity consumers, whose diagrams carry `boundaryWord_geodesic`, are
served by the weaker hypothesis exactly as before. -/
theorem hasQuasiGeodesicSpelling_of_hasGeodesicBoundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R)
    (hgeo : Z.HasGeodesicBoundaryLength) :
    Z.HasQuasiGeodesicSpelling := by
  obtain ⟨outer, houter, hmap⟩ :=
    exists_geodesicSpelling_of_hasGeodesicBoundaryLength Z hgeo
  refine ⟨outer, hmap, ?_, ?_⟩
  · simpa using houter.2.1
  · exact isLambdaCQuasiGeodesicWord_of_isGeodesicWord D houter
      (by norm_num) (by norm_num)

/-! ## The statement -/

/-- **Osin's Lemma 4.4 in certificate form, at diagrams whose designated
boundary word has an admissible quasi-geodesic spelling.**  This is the
weakest boundary hypothesis under which the estimating route proves the
certificate. -/
def RelativeGreendlingerQuasiGeodesicSpellingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
            RelWord.IsLemma44Input D W eps mu rho →
              ∀ Z : RelativeReducedDiagram D W R,
                Z.HasQuasiGeodesicSpelling →
                  Nonempty (RelativeDiagramCertificate D W eps mu Z)

/-- **The main reduction at the weakest boundary hypothesis.**  Hypotheses are
est's three construction propositions, the vk realization at a supplied
spelling, and the supplied-word arc conversion — the same list as
`relativeGreendlingerGeodesicLengthStatement_of_components`, with the boundary
clause weakened. -/
theorem relativeGreendlingerQuasiGeodesicSpellingStatement_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{u, w, 0})
    (hreal : RelativeDiscRealizationSpellingStatement.{u, w})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{u, w}) :
    RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  have hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hD
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_components
      hselection hpieces hunbound D hhyper (1 / 4) 1 mu
      (by norm_num) (by norm_num) (by norm_num) hmu hmuUpper
  refine ⟨eps, rho, ?_⟩
  intro rho' hrho' W R hinput Z hspell
  have hinput0 : RelWord.IsLemma44Input D W eps mu rho :=
    hinput.mono_parameters le_rfl le_rfl hrho'
  have hcondition :
      GGT.VanKampen.OsinCCondition D W eps mu (1 / 4) 1 rho :=
    hinput0.toOsinCCondition
  obtain ⟨outer, hmap, houterVal, hqgOuter⟩ := hspell
  obtain ⟨Creal⟩ := hreal D W R Z outer hqgOuter.1 houterVal
  have hqg : IsLambdaCQuasiGeodesicWord D (1 / 4) 1
      Creal.diagram.boundaryWord := by
    rw [Creal.outerWord_eq]
    exact hqgOuter
  obtain ⟨Delta, hequivNonempty, faces, Gamma, htarget, hlarge⟩ :=
    hgood W hcondition Creal.diagram Creal.reduced
      Creal.rCellCount_pos hqg
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
  obtain ⟨C, hC⟩ :=
    hconv D eps Delta Z.boundaryWord outer hboundaryWord hmap Gamma.source
      packaged
      ((Z.cells.get
        (Creal.cellIndex.symm (hequiv.cellIndex.symm Gamma.source))).relator)
      hword
  refine ⟨RelativeDiagramCertificate.ofLargeCell
    (Creal.cellIndex.symm (hequiv.cellIndex.symm Gamma.source)) C ?_⟩
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

/-! ## Relations to the two neighbouring statements -/

/-- The quasi-geodesic-spelling statement implies the geodesic-length one, so
it subsumes `HullSCRelativeGreendlingerGeodesicConsumers` and every consumer
flipped onto it. -/
theorem relativeGreendlingerGeodesicLengthStatement_of_quasiGeodesicSpelling
    (h : RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, w}) :
    RelativeGreendlingerGeodesicLengthStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  obtain ⟨eps, rho0, hgood⟩ := h D hD mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho W R hinput Z hgeo
  exact hgood rho hrho W R hinput Z
    (hasQuasiGeodesicSpelling_of_hasGeodesicBoundaryLength Z hgeo)

/-- The unrestricted statement implies it, so a future proof of
`RelativeGreendlingerStatement` still serves everything downstream. -/
theorem relativeGreendlingerQuasiGeodesicSpellingStatement_of_relativeGreendlingerStatement
    (h : RelativeGreendlingerStatement.{u, w}) :
    RelativeGreendlingerQuasiGeodesicSpellingStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  obtain ⟨eps, rho0, hgood⟩ := h D hD mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho W R hinput Z _
  exact hgood rho hrho W R hinput Z

/-! ## What Hull's Lemma 4.9 still owes -/

/-- **The clause the Lemma 4.9 chain has to supply.**  Its diagrams are
`Lemma49GeodesicPowerDiagram.toRelativeReducedDiagram`, whose boundary word is
a power of a geodesic word for `g` and whose designated boundary is `g ^ n`.
Supplying a quasi-geodesic spelling there is exactly Hull's translation-gap
case analysis; it is not a consequence of the power diagram's fields, and the
geodesic clause is outright false for it once `g` is not translation-like.

Naming it separates that geometric obligation from the certificate machinery,
which no longer carries any boundary hypothesis of its own. -/
def PowerBoundaryQuasiGeodesicSpellingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : Lemma49GeodesicPowerDiagram D v g n),
    Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling

/-- **Model check.**  At `n = 1` the power boundary is the geodesic word
itself, so the clause holds with no translation gap: the obligation is about
genuine powers. -/
theorem hasQuasiGeodesicSpelling_toRelativeReducedDiagram_one
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G}
    (Z : Lemma49GeodesicPowerDiagram D v g 1) :
    Z.toRelativeReducedDiagram.HasQuasiGeodesicSpelling := by
  refine ⟨Z.boundaryWord, ?_, ?_, ?_⟩
  · show Z.boundaryWord.map GGT.RelLetter.val =
      (lemma49BoundaryPower Z.boundaryWord 1).map GGT.RelLetter.val
    simp [lemma49BoundaryPower]
  · show GGT.RelLetter.listVal Z.boundaryWord = g ^ 1
    rw [pow_one]
    simpa using Z.boundary_geodesic.2.1
  · exact isLambdaCQuasiGeodesicWord_of_isGeodesicWord D Z.boundary_geodesic
      (by norm_num) (by norm_num)

end HullSC
end GroupApproximation
