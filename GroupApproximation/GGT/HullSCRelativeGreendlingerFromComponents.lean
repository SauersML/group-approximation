import GroupApproximation.GGT.HullSCLemma44RelativeGreendlingerAdapter
import GroupApproximation.GGT.HullSCLemma49SourceGreendlinger
import GroupApproximation.GGT.HullSCRelatorSeparation2PublishedReduction
import GroupApproximation.GGT.CayleyFourPointConverse

/-!
# Relative Greendlinger from the estimating components

`HullSC.RelativeGreendlingerStatement` is the algebraic certificate form of
Osin's Lemma 4.4 consumed throughout `GGT/HullSCLemma44*` and
`GGT/HullSCLemma49*`.  The source-faithful form of the same lemma,
`GGT.VanKampen.RelativeGreendlingerQuasiGeodesicStatement`, **is** proved from
est's three construction propositions by
`GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_components`, and
`GGT.VanKampen.relativeDiscRealizationStatement` transports it to an algebraic
reduced diagram.  This module closes the remaining distance.

## The boundary hypothesis is not optional

`RelativeReducedDiagram` imposes no geometry on its designated boundary word:
its docstring says so outright, and its only length clause is
`boundaryWord.length ≤ 2 * R`.  The source theorem, on the other hand, applies
to a planar disc whose outer word is a `(lambda,c)`-quasi-geodesic *relative*
word, and `GGT.VanKampen.IsLambdaCQuasiGeodesicWord` carries
`RelWord.IsAdmissible` as its first conjunct.  Through
`RelativeDiscRealization.outerWord_eq` the outer word of a realization is
`Z.boundaryWord.map GGT.RelLetter.base`, so the source theorem needs every
letter of `Z.boundaryWord` to lie in `D.base` and the resulting relative word
to be quasi-geodesic.  Neither follows from the fields of
`RelativeReducedDiagram`.

`RelativeReducedDiagram.HasBaseGeodesicBoundary` names exactly that missing
hypothesis, and `RelativeGreendlingerBaseGeodesicStatement` is
`RelativeGreendlingerStatement` restricted to diagrams that carry it.  The
restriction is strictly weaker
(`relativeGreendlingerBaseGeodesicStatement_of_relativeGreendlingerStatement`)
and it is the form the consumers can actually feed: every diagram reaching
`HullSC.injOn_relativeBall_of_relativeDiagramCertificates` is
`Z.toRelativeReducedDiagram D` for a `Lemma44OrientedRelatorDiagram`, whose
`boundaryWord_geodesic` field the coercion discards.

## What is left

`RelativeExteriorArcConversionStatement` is the single residue: one planar
exterior region converts to one algebraic boundary contiguity on the same
designated boundary word, with an exterior arc at least as long.  It is
strictly smaller than `VkRelativeDiagramCertificateData`, which asks for the
conversion data at *every* cell and at *every* embedded contiguity together
with the option-level agreement equation `relative_eq`; the certificate needs
a contiguity only at the large cell, because
`RelativeDiagramCertificate.contiguity` is `Option`-valued and may be `none`
everywhere else.  `RelativeDiagramCertificate.ofLargeCell` performs that
packaging here.

The residue is not vacuous and not free: `RelativeBoundaryContiguity.empty`
shows every relator carries the empty-exterior contiguity, so the whole
content of the residue is the length inequality on the exterior arc.

Every declaration below is a complete proof or a named proposition; no
placeholder of any kind is introduced here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.VanKampen

universe u w

/-! ## The boundary hypothesis the source theorem needs -/

/-- **The boundary geometry `RelativeReducedDiagram` drops.**  Reading the
designated boundary word as a relative word over base letters, it is geodesic
from `1` to the designated boundary element.  `Lemma44RelatorDiagramBoundary`
carries `boundaryWord_geodesic`, but only as an equality of *lengths* in
`A.carrier`; the relative reading also asserts that every boundary letter is a
letter of `D.base`. -/
def RelativeReducedDiagram.HasBaseGeodesicBoundary
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R) : Prop :=
  GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary
    (Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))

/-- **Osin's Lemma 4.4 in certificate form, at diagrams whose designated
boundary is a geodesic relative word over base letters.**  Every clause is the
clause of `RelativeGreendlingerStatement`; the single added hypothesis is the
boundary geometry the source proof uses. -/
def RelativeGreendlingerBaseGeodesicStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
            RelWord.IsLemma44Input D W eps mu rho →
              ∀ Z : RelativeReducedDiagram D W R,
                Z.HasBaseGeodesicBoundary →
                  Nonempty (RelativeDiagramCertificate D W eps mu Z)

/-- **The restricted form is strictly weaker.**  Its conclusion is reached
under one extra hypothesis and nothing else changes. -/
theorem relativeGreendlingerBaseGeodesicStatement_of_relativeGreendlingerStatement
    (h : RelativeGreendlingerStatement.{u, w}) :
    RelativeGreendlingerBaseGeodesicStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  obtain ⟨eps, rho0, hgood⟩ := h D hD mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho W R hinput Z _
  exact hgood rho hrho W R hinput Z

/-- **The added clause has content.**  A designated boundary word carrying a
letter outside `D.base` cannot satisfy it: the base reading of that letter is
not an admissible relative letter, and
`GGT.OsinComponents.IsGeodesicWord` asserts admissibility.  So the restriction
is a real one and not a bookkeeping device. -/
theorem not_hasBaseGeodesicBoundary_of_not_mem_base
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R} {x : G}
    (hx : x ∈ Z.boundaryWord) (hbase : x ∉ D.base) :
    ¬ Z.HasBaseGeodesicBoundary := by
  intro h
  have h' : GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary
      (Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) := h
  exact hbase (h'.1 (GGT.RelLetter.base x) (List.mem_map.mpr ⟨x, hx, rfl⟩))

/-- **The exact remaining distance between the restricted and unrestricted
statements**, as a named proposition: every common reduced diagram has a
designated boundary word that is a geodesic relative word over base letters.
`RelativeReducedDiagram` has no field implying it. -/
def AllReducedDiagramsHaveBaseGeodesicBoundary : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R), Z.HasBaseGeodesicBoundary

/-- **The two propositions together are the unrestricted statement.**  So the
distance from the estimating components to `RelativeGreendlingerStatement`
splits into the reduction proved below and this boundary universality. -/
theorem relativeGreendlingerStatement_of_baseGeodesicStatement
    (h : RelativeGreendlingerBaseGeodesicStatement.{u, w})
    (hall : AllReducedDiagramsHaveBaseGeodesicBoundary.{u, w}) :
    RelativeGreendlingerStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  obtain ⟨eps, rho0, hgood⟩ := h D hD mu hmu hmuUpper
  refine ⟨eps, rho0, ?_⟩
  intro rho hrho W R hinput Z
  exact hgood rho hrho W R hinput Z (hall D Z)

/-! ## The empty-exterior contiguity -/

/-- **Every relator carries the empty-exterior boundary contiguity.**  The
relator decomposes as `[] ++ relator`, the boundary as `[] ++ [] ++
boundaryWord`, and both sides are empty, so the value equation is `1 = 1`.
Consequently the content of a contiguity is entirely in the *length* of its
exterior arc, which is what the conversion residue below has to supply. -/
def RelativeBoundaryContiguity.empty
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    (boundaryWord : List G) (relator : List (GGT.RelLetter G Lambda)) :
    RelativeBoundaryContiguity D eps boundaryWord relator where
  exterior := []
  remainder := relator
  relator_decomposition := by simp
  boundaryBefore := []
  boundaryArc := []
  boundaryAfter := boundaryWord
  boundary_decomposition := by simp
  leftSide := []
  rightSide := []
  leftSide_admissible := by
    intro a ha
    simp at ha
  rightSide_admissible := by
    intro a ha
    simp at ha
  leftSide_short := by simp
  rightSide_short := by simp
  exterior_value := by
    simp [GGT.RelLetter.listVal_nil]

/-- The empty-exterior contiguity has exterior length zero. -/
@[simp]
theorem RelativeBoundaryContiguity.empty_exterior_length
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps : ℕ)
    (boundaryWord : List G) (relator : List (GGT.RelLetter G Lambda)) :
    (RelativeBoundaryContiguity.empty D eps boundaryWord relator).exterior.length
      = 0 := rfl

/-! ## Packaging a certificate from a single large cell -/

/-- **A certificate needs a contiguity only at its large cell.**
`RelativeDiagramCertificate.contiguity` is `Option`-valued, so every other
cell may be assigned `none`.  This is why the conversion residue below is a
one-cell statement rather than a whole-diagram family. -/
def RelativeDiagramCertificate.ofLargeCell
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R eps : ℕ} {mu : ℝ}
    {Z : RelativeReducedDiagram D W R}
    (i : Fin Z.cells.length)
    (C : RelativeBoundaryContiguity D eps Z.boundaryWord
      (Z.cells.get i).relator)
    (hlarge : (1 - 23 * mu) * (((Z.cells.get i).relator).length : ℝ)
      ≤ (C.exterior.length : ℝ)) :
    RelativeDiagramCertificate D W eps mu Z where
  boundaryWord := Z.boundaryWord
  boundaryWord_eq := rfl
  cellLabel := fun k => (Z.cells.get k).relator
  cellLabel_rotate := fun _ => ⟨0, by simp⟩
  cellLabel_mem := fun k => (Z.cells.get k).relator_mem
  contiguity := fun k => if h : i = k then some (h ▸ C) else none
  largeCell := by
    refine ⟨i, C, ?_, hlarge⟩
    simp

/-- **A certificate whose labels are a common cyclic permutation of the
relators.**  The planar side of Osin's argument delivers a *cyclic* arc of the
source cell's dart cycle, while `RelativeBoundaryContiguity.relator_decomposition`
asks the exterior to be a prefix; rotating every label by the same amount turns
the cyclic subword into a prefix.  Membership is preserved because
`RelWord.IsSmallCancellation` requires the family to be closed under cyclic
permutation, which is the `rotate_mem` hypothesis below. -/
def RelativeDiagramCertificate.ofLargeCellRotated
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R eps : ℕ} {mu : ℝ}
    {Z : RelativeReducedDiagram D W R}
    (hrotate : ∀ v ∈ W, ∀ m : ℕ, v.rotate m ∈ W)
    (i : Fin Z.cells.length) (n : ℕ)
    (C : RelativeBoundaryContiguity D eps Z.boundaryWord
      (((Z.cells.get i).relator).rotate n))
    (hlarge : (1 - 23 * mu) *
        ((((Z.cells.get i).relator).rotate n).length : ℝ)
      ≤ (C.exterior.length : ℝ)) :
    RelativeDiagramCertificate D W eps mu Z where
  boundaryWord := Z.boundaryWord
  boundaryWord_eq := rfl
  cellLabel := fun k => ((Z.cells.get k).relator).rotate n
  cellLabel_rotate := fun _ => ⟨n, rfl⟩
  cellLabel_mem := fun k => hrotate _ ((Z.cells.get k).relator_mem) n
  contiguity := fun k => if h : i = k then some (h ▸ C) else none
  largeCell := by
    refine ⟨i, C, ?_, hlarge⟩
    simp

/-! ## Transporting a planar cell index to its algebraic cell -/

/-- **The planar relator word at a cell of an `O`-equivalent diagram is the
algebraic relator of the corresponding cell.**  The two index equivalences are
`RelativeDiscRealization.cellIndex` and `OEquivalentDiscDiagram.cellIndex`, and
the two word equations compose. -/
theorem cellWord_eq_relator_of_oEquivalent
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    (hreal : RelativeDiscRealization D W Z)
    {Delta : DiscDiagram.{u, w, 0} W}
    (hequiv : OEquivalentDiscDiagram hreal.diagram Delta)
    (j : Fin Delta.rCellCount) :
    (GGT.VanKampen.Embedded.cell Delta j).word =
      (Z.cells.get (hreal.cellIndex.symm (hequiv.cellIndex.symm j))).relator := by
  have hplanar :
      (GGT.VanKampen.Embedded.cell Delta
          (hequiv.cellIndex (hequiv.cellIndex.symm j))).word =
        (GGT.VanKampen.Embedded.cell hreal.diagram
          (hequiv.cellIndex.symm j)).word :=
    hequiv.cellWord_eq (hequiv.cellIndex.symm j)
  rw [Equiv.apply_symm_apply] at hplanar
  have halgebraic :
      (hreal.diagram.relatorCells.get
          (hreal.cellIndex
            (hreal.cellIndex.symm (hequiv.cellIndex.symm j)))).word =
        (Z.cells.get
          (hreal.cellIndex.symm (hequiv.cellIndex.symm j))).relator :=
    hreal.cellWord_eq (hreal.cellIndex.symm (hequiv.cellIndex.symm j))
  rw [Equiv.apply_symm_apply] at halgebraic
  rw [hplanar]
  exact halgebraic

/-! ## The one remaining conversion -/

/-- **The single residue between the source theorem and the algebraic
certificate.**

A planar exterior region on a disc diagram whose outer word is the base
reading of `boundaryWord` converts to an algebraic boundary contiguity on
`boundaryWord` for the same relator, with an exterior arc no shorter than the
planar source arc.

This is strictly smaller than `VkRelativeDiagramCertificateData`: no family
over all cells, no `data` field at every embedded contiguity, and no
`relative_eq` agreement between the two option families.  It is also stated
without mentioning `RelativeReducedDiagram`, so it is a statement about disc
diagrams alone.

`RelativeBoundaryContiguity.empty` shows the existential is inhabited for
every relator, so the entire content of this proposition is the length
inequality. -/
def RelativeExteriorArcConversionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, 0} W) (boundaryWord : List G),
    Delta.boundaryWord =
        boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda) →
      ∀ (j : Fin Delta.rCellCount)
        (Gamma : EmbeddedBoundaryContiguity D eps Delta j)
        (relator : List (GGT.RelLetter G Lambda)),
        (GGT.VanKampen.Embedded.cell Delta j).word = relator →
          ∃ C : RelativeBoundaryContiguity D eps boundaryWord relator,
            Gamma.region.sourceArc.length ≤ C.exterior.length

/-- **Model test for the residue.**  At a region whose planar source arc is
empty the conversion is discharged by the empty-exterior contiguity, with no
geometry at all.  So the residue's hypotheses are consistent and its content
is exactly the positive-length case. -/
theorem exists_relativeBoundaryContiguity_of_sourceArc_length_zero
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) {Delta : DiscDiagram.{u, w, 0} W} (boundaryWord : List G)
    {j : Fin Delta.rCellCount}
    (Gamma : EmbeddedBoundaryContiguity D eps Delta j)
    (relator : List (GGT.RelLetter G Lambda))
    (harc : Gamma.region.sourceArc.length = 0) :
    ∃ C : RelativeBoundaryContiguity D eps boundaryWord relator,
      Gamma.region.sourceArc.length ≤ C.exterior.length := by
  refine ⟨RelativeBoundaryContiguity.empty D eps boundaryWord relator, ?_⟩
  rw [harc]
  exact Nat.zero_le _

/-! ## The numerical step between the two published coefficients -/

/-- Osin's estimating theorem produces the strict degree `1 - 13 * mu`; the
certificate consumed by Hull's Lemma 4.4 asks for `1 - 23 * mu`.  The second
is weaker at every nonnegative length whenever `mu` is nonnegative. -/
theorem mul_le_mul_of_twentyThree_le_thirteen
    {mu : ℝ} (hmu : 0 ≤ mu) (n : ℕ) :
    (1 - 23 * mu) * (n : ℝ) ≤ (1 - 13 * mu) * (n : ℝ) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith [mul_nonneg hmu hn]

/-! ## The main reduction -/

/-- **`RelativeGreendlingerBaseGeodesicStatement` from est's three
construction propositions and the one conversion residue.**

The vk realization statement is not a hypothesis: it is proved, as
`GGT.VanKampen.relativeDiscRealizationStatement`.  The parameters handed to the
source theorem are Osin's own `(lambda, c) = (1/4, 1)`, which is exactly the
pair `RelWord.IsLemma44Input.toOsinCCondition` supplies. -/
theorem relativeGreendlingerBaseGeodesicStatement_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{u, w, 0})
    (hconv : RelativeExteriorArcConversionStatement.{u, w}) :
    RelativeGreendlingerBaseGeodesicStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  have hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hD
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    exists_realized_embeddedBoundaryContiguity_of_components_and_geodesicBoundary
      hselection hpieces hunbound
      GGT.VanKampen.relativeDiscRealizationStatement
      D hhyper (lambda := 1 / 4) (c := 1)
      (by norm_num) (by norm_num) (by norm_num) hmu hmuUpper
  refine ⟨eps, rho, ?_⟩
  intro rho' hrho' W R hinput Z hboundary
  have hinput0 : RelWord.IsLemma44Input D W eps mu rho :=
    hinput.mono_parameters le_rfl le_rfl hrho'
  have hcondition :
      GGT.VanKampen.OsinCCondition D W eps mu (1 / 4) 1 rho :=
    hinput0.toOsinCCondition
  obtain ⟨hreal, Delta, j, Gamma, hequivNonempty, _hsource, _htarget, hlarge⟩ :=
    hgood W hcondition R Z hboundary
  obtain ⟨hequiv⟩ := hequivNonempty
  have hword : (GGT.VanKampen.Embedded.cell Delta j).word =
      (Z.cells.get
        (hreal.cellIndex.symm (hequiv.cellIndex.symm j))).relator :=
    cellWord_eq_relator_of_oEquivalent hreal hequiv j
  have hboundaryWord : Delta.boundaryWord =
      Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda) :=
    hequiv.boundaryWord_eq.trans hreal.outerWord_eq
  obtain ⟨C, hC⟩ :=
    hconv D eps Delta Z.boundaryWord hboundaryWord j Gamma
      ((Z.cells.get
        (hreal.cellIndex.symm (hequiv.cellIndex.symm j))).relator) hword
  refine ⟨RelativeDiagramCertificate.ofLargeCell
    (hreal.cellIndex.symm (hequiv.cellIndex.symm j)) C ?_⟩
  have hlengthEq :
      (((Z.cells.get
          (hreal.cellIndex.symm (hequiv.cellIndex.symm j))).relator).length : ℝ) =
        (((GGT.VanKampen.Embedded.cell Delta j).word).length : ℝ) := by
    rw [hword]
  have hstep :
      (1 - 23 * mu) * (((GGT.VanKampen.Embedded.cell Delta j).word).length : ℝ)
        ≤ (1 - 13 * mu) *
          (((GGT.VanKampen.Embedded.cell Delta j).word).length : ℝ) :=
    mul_le_mul_of_twentyThree_le_thirteen hmu.le _
  have hCreal : (Gamma.region.sourceArc.length : ℝ) ≤ (C.exterior.length : ℝ) :=
    Nat.cast_le.mpr hC
  rw [hlengthEq]
  exact le_trans hstep (le_trans (le_of_lt hlarge) hCreal)

/-- **The unrestricted statement from the estimating components and the two
named residues.**  This is the composite the manuscript lane asked for: the
three est construction propositions, the one-cell arc conversion, and the
boundary universality.  The vk realization statement does not appear, being
proved. -/
theorem hullSC_relativeGreendlingerStatement_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{u, w, 0})
    (hconv : RelativeExteriorArcConversionStatement.{u, w})
    (hall : AllReducedDiagramsHaveBaseGeodesicBoundary.{u, w}) :
    RelativeGreendlingerStatement.{u, w} :=
  relativeGreendlingerStatement_of_baseGeodesicStatement
    (relativeGreendlingerBaseGeodesicStatement_of_components
      hselection hpieces hunbound hconv)
    hall

/-! ## Consumers reached by the restricted statement -/

/-- **The added clause is exactly about peripheral letters on the boundary.**
If the relative alphabet adds nothing to the base then every geodesic
designated boundary word satisfies the clause, so the restriction bites only
on diagrams whose boundary word reads a letter of a peripheral subgroup that
is not already a base letter. -/
theorem hasBaseGeodesicBoundary_of_alphabet_carrier_subset_base
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (hsub : D.alphabet.carrier ⊆ D.base)
    (Z : RelativeReducedDiagram D W R)
    (hgeo : Z.boundaryWord.length
      = WordMetric.wordNorm D.alphabet.carrier Z.boundary) :
    Z.HasBaseGeodesicBoundary := by
  show GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary
    (Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact hsub (Z.boundaryWord_isWord.letters x hx)
  · rw [listVal_map_base, one_mul]
    exact Z.boundaryWord_isWord.prod_eq
  · have hlen : (Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)).length
          = Z.boundaryWord.length := by simp
    have hdist : WordMetric.wordDist D.alphabet.carrier 1 Z.boundary
        = WordMetric.wordNorm D.alphabet.carrier Z.boundary :=
      WordMetric.wordDist_one_left _ _
    rw [hlen, hdist]
    exact hgeo

/-- The base reading of a word of group elements spells its product; this is
`HullSC.listVal_map_base` of `GGT/HullSCRelatorWord.lean`. -/
example {G : Type u} [Group G] {Lambda : Type w} (l : List G) :
    GGT.RelLetter.listVal
        (l.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))
      = l.prod := listVal_map_base l

/-- **Hull's Lemma 4.4 diagrams satisfy the added hypothesis whenever their
geodesic boundary word is spelled by base letters.**  The coercion
`Lemma44OrientedRelatorDiagram.toRelativeReducedDiagram` keeps the boundary
word and its value, and `boundaryWord_geodesic` is its length equation, so the
only thing to supply is admissibility of the base reading. -/
theorem hasBaseGeodesicBoundary_toRelativeReducedDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram D.alphabet W R)
    (hbase : ∀ x ∈ Z.boundaryWord, x ∈ D.base) :
    (Z.toRelativeReducedDiagram D).HasBaseGeodesicBoundary := by
  show GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary
    (Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact hbase x hx
  · rw [listVal_map_base, one_mul]
    exact Z.boundaryWord_isWord.prod_eq
  · have hlen : (Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)).length
          = Z.boundaryWord.length := by simp
    have hdist : WordMetric.wordDist D.alphabet.carrier 1 Z.boundary
        = WordMetric.wordNorm D.alphabet.carrier Z.boundary :=
      WordMetric.wordDist_one_left _ _
    rw [hlen, hdist]
    exact Z.boundaryWord_geodesic

end HullSC
end GroupApproximation
