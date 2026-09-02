import GroupApproximation.GGT.HullSCRelativeGreendlingerQuasiGeodesicSpelling

/-!
# Relative Greendlinger at a power boundary

`HullSCRelativeGreendlingerQuasiGeodesicSpelling` states the boundary clause
with the quasi-geodesic constants pinned to `(1/4, 1)`.  That is right for a
geodesic boundary word, where the additive error is zero, but **too strong for
Hull's Lemma 4.9**: the estimates available for a power of a geodesic word are

* `isLambdaCQuasiGeodesicWord_power_of_long_period` — `(1/4, 8*delta + 2)`;
* `isLambdaCQuasiGeodesicWord_power_of_stableTranslation` — `(1/M, 4*L)`.

Both carry an additive constant far larger than one, so the pinned form cannot
receive them.

The constant cannot simply be existentially quantified per diagram either:
`GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_components` chooses `eps`
and `rho` **after** `lambda` and `c` and **before** the diagram, so the
certificate parameters depend on the quasi-geodesic constants.  The honest
shape therefore fixes `c` up front, which is exactly how the Lemma 4.9 branches
work: they fix `delta` first and then obtain `c = 8*delta + 2`.

`RelativeGreendlingerQuasiGeodesicSpellingAtStatement` is that shape, and
`hasQuasiGeodesicSpellingAt_toRelativeReducedDiagram_of_longPeriod` discharges
the boundary clause outright for the long-period branch from the landed power
estimate.  So what Leaf C owes is no longer a boundary hypothesis about
`RelativeReducedDiagram` at all; it is the branch hypothesis Hull's proof
already establishes.

Every declaration below is a complete proof or a named proposition; no
placeholder of any kind is introduced here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.VanKampen

universe u w

/-! ## The boundary clause at arbitrary quasi-geodesic constants -/

/-- **The designated boundary word has an admissible `(lambda, c)`-quasi-geodesic
relative spelling.**  `HasQuasiGeodesicSpelling` is the case `(1/4, 1)`. -/
def RelativeReducedDiagram.HasQuasiGeodesicSpellingAt
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R) (lambda c : ℝ) : Prop :=
  ∃ outer : List (GGT.RelLetter G Lambda),
    outer.map GGT.RelLetter.val = Z.boundaryWord ∧
      GGT.RelLetter.listVal outer = Z.boundary ∧
        IsLambdaCQuasiGeodesicWord D lambda c outer

/-- The pinned clause is the case `(1/4, 1)`. -/
theorem hasQuasiGeodesicSpellingAt_of_hasQuasiGeodesicSpelling
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    (h : Z.HasQuasiGeodesicSpelling) :
    Z.HasQuasiGeodesicSpellingAt (1 / 4) 1 := h

/-! ## The statement, with the constants fixed before the diagram -/

/-- **Osin's Lemma 4.4 in certificate form, at a fixed additive constant.**
`c` is chosen before `eps` and `rho`, because the source theorem chooses its
parameters after the quasi-geodesic constants and before the diagram. -/
def RelativeGreendlingerQuasiGeodesicSpellingAtStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∀ c : ℝ, 1 ≤ c →
          ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
            ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
              RelWord.IsLemma44Input D W eps mu rho →
                ∀ Z : RelativeReducedDiagram D W R,
                  Z.HasQuasiGeodesicSpellingAt (1 / 4) c →
                    Nonempty (RelativeDiagramCertificate D W eps mu Z)

/-- **The reduction at a fixed additive constant.**  Same hypothesis list as
the pinned form; the small-cancellation input is fed to the source theorem
through `RelWord.IsLemma44Input.toOsinCCondition_of_weakerConstants`, which is
exactly the monotonicity that lets `c` grow. -/
theorem relativeGreendlingerQuasiGeodesicSpellingAtStatement_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{u, w, 0})
    (hreal : RelativeDiscRealizationSpellingStatement.{u, w})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{u, w}) :
    RelativeGreendlingerQuasiGeodesicSpellingAtStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper c hc
  have hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hD
  have hcNonneg : (0 : ℝ) ≤ c := le_trans (by norm_num) hc
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_components
      hselection hpieces hunbound D hhyper (1 / 4) c mu
      (by norm_num) (by norm_num) hcNonneg hmu hmuUpper
  refine ⟨eps, rho, ?_⟩
  intro rho' hrho' W R hinput Z hspell
  have hinput0 : RelWord.IsLemma44Input D W eps mu rho :=
    hinput.mono_parameters le_rfl le_rfl hrho'
  have hcondition :
      GGT.VanKampen.OsinCCondition D W eps mu (1 / 4) c rho :=
    hinput0.toOsinCCondition_of_weakerConstants le_rfl hc
  obtain ⟨outer, hmap, houterVal, hqgOuter⟩ := hspell
  obtain ⟨Creal⟩ := hreal D W R Z outer hqgOuter.1 houterVal
  have hqg : IsLambdaCQuasiGeodesicWord D (1 / 4) c
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

/-! ## The power boundary, discharged on the long-period branch -/

/-- **What Leaf C owed, discharged.**

For a geodesic power diagram the spelling is the power word itself: the
letterwise correspondence is definitional, since
`Lemma49GeodesicPowerDiagram.toRelativeReducedDiagram` sets its boundary word
to be exactly that word's letter values, and the value is `g ^ n` by
`listVal_lemma49BoundaryPower`.  The only content is quasi-geodesicity of the
power, and on the long-period branch that is the landed estimate
`isLambdaCQuasiGeodesicWord_power_of_long_period`.

So the Lemma 4.9 chain no longer owes a boundary hypothesis about an arbitrary
reduced diagram; it owes only the branch hypotheses its own proof already
establishes. -/
theorem hasQuasiGeodesicSpellingAt_toRelativeReducedDiagram_of_longPeriod
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n delta : ℕ}
    (Z : Lemma49GeodesicPowerDiagram D v g n)
    (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    (hn : 0 < n)
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (hlong : 8 * delta + 2 ≤ Z.boundaryWord.length) :
    Z.toRelativeReducedDiagram.HasQuasiGeodesicSpellingAt (1 / 4)
      ((8 * delta + 2 : ℕ) : ℝ) := by
  refine ⟨lemma49BoundaryPower Z.boundaryWord n, rfl, ?_, ?_⟩
  · show GGT.RelLetter.listVal (lemma49BoundaryPower Z.boundaryWord n) = g ^ n
    have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
      simpa using Z.boundary_geodesic.2.1
    rw [listVal_lemma49BoundaryPower, hvalue]
  · exact isLambdaCQuasiGeodesicWord_power_of_long_period D N hshort
      Z.boundary_geodesic hn hdelta hlong

/-- **Model check, kept from the pinned form.**  At `n = 1` the power boundary
is the geodesic word itself, so the clause holds with no translation gap and
with the geodesic constants. -/
theorem hasQuasiGeodesicSpellingAt_toRelativeReducedDiagram_one
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G}
    (Z : Lemma49GeodesicPowerDiagram D v g 1) :
    Z.toRelativeReducedDiagram.HasQuasiGeodesicSpellingAt (1 / 4) 1 :=
  hasQuasiGeodesicSpellingAt_of_hasQuasiGeodesicSpelling
    (hasQuasiGeodesicSpelling_toRelativeReducedDiagram_one Z)

end HullSC
end GroupApproximation
