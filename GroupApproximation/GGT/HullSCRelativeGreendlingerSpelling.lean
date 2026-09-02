import GroupApproximation.GGT.HullSCRelativeGreendlingerFromComponents
import GroupApproximation.GGT.HullSCLemma44OriginalExpansion

/-!
# Relative Greendlinger through an admissible boundary spelling

`HullSCRelativeGreendlingerFromComponents` reduces
`HullSC.RelativeGreendlingerStatement` to est's three construction
propositions and two residues, one of which,
`AllReducedDiagramsHaveBaseGeodesicBoundary`, asks every designated boundary
word to be spelled by letters of `D.base`.  That residue is **not
dischargeable**: the diagrams reaching
`HullSC.injOn_relativeBall_of_relativeDiagramCertificates` come from
`exists_lemma44ReducedRelatorDiagram_of_not_injOn` over `D.alphabet`, whose
words range over `D.base ∪ ⋃ H λ`, and
`not_hasBaseGeodesicBoundary_of_not_mem_base` shows one peripheral letter
refutes the clause.

The obstruction is not mathematical.  It comes from a single design choice:
`GGT.VanKampen.RelativeDiscRealization.outerWord_eq` pins the realized outer
word to `Z.boundaryWord.map GGT.RelLetter.base`, and the cactus that proves
`relativeDiscRealizationStatement` hard-codes that reading in
`GGT.VanKampen.RelativeReducedDiagram.outerFaceWord`.  Nothing in the cactus
uses the reading beyond `GGT.RelLetter.listVal` of the outer word, so the same
construction realizes *any* relative word spelling the designated boundary.

This module carries out that generalization on the algebraic side.
`RelativeDiscRealizationAtWord` is the realization at a supplied outer word and
`RelativeDiscRealizationSpellingStatement` is the corresponding vk residue.
Against it the boundary hypothesis weakens from "spelled by base letters and
geodesic" to `RelativeReducedDiagram.HasGeodesicBoundaryLength`, a clause about
lengths only — and that clause **is** discharged for every Hull Lemma 4.4
diagram by `hasGeodesicBoundaryLength_toRelativeReducedDiagram`, with no side
hypothesis, because it is exactly the `boundaryWord_geodesic` field that
`Lemma44OrientedRelatorDiagram.toRelativeReducedDiagram` discards.

So the trade is: one residue that cannot be discharged is replaced by one that
is discharged here, at the price of asking vk for its realization at a supplied
spelling rather than at the base reading.

Every declaration below is a complete proof or a named proposition; no
placeholder of any kind is introduced here.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT.VanKampen

universe u w

/-! ## Letterwise spellings over the relative alphabet -/

/-- **Every word over the relative alphabet has a letterwise admissible
spelling.**  This strengthens `exists_word_of_alphabetList`, which records the
length and the value but not the letterwise correspondence; the correspondence
is what lets an arc of the spelling be transported to an arc of the original
`List G` boundary word. -/
theorem exists_letterwise_spelling
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (l : List G)
    (hl : ∀ x ∈ l, x ∈ D.alphabet.carrier) :
    ∃ word : List (GGT.RelLetter G Lambda),
      RelWord.IsAdmissible D word ∧
        word.map GGT.RelLetter.val = l := by
  induction l with
  | nil =>
      refine ⟨[], ?_, rfl⟩
      intro a ha
      simp at ha
  | cons x t ih =>
      obtain ⟨a, ha, hav⟩ :=
        exists_relLetter_of_mem_alphabet D (hl x (by simp))
      obtain ⟨word, hword, hmap⟩ :=
        ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
      refine ⟨a :: word, ?_, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with hb | hb
        · rw [hb]
          exact ha
        · exact hword b hb
      · rw [List.map_cons, hav, hmap]

/-- A letterwise spelling has the length of the word it spells. -/
theorem length_of_letterwise_spelling
    {G : Type u} {Lambda : Type w}
    {l : List G} {word : List (GGT.RelLetter G Lambda)}
    (hmap : word.map GGT.RelLetter.val = l) : word.length = l.length := by
  have h := congrArg List.length hmap
  simpa using h

/-- A letterwise spelling spells the product of the word it spells. -/
theorem listVal_of_letterwise_spelling
    {G : Type u} [Group G] {Lambda : Type w}
    {l : List G} {word : List (GGT.RelLetter G Lambda)}
    (hmap : word.map GGT.RelLetter.val = l) :
    GGT.RelLetter.listVal word = l.prod := by
  unfold GGT.RelLetter.listVal
  rw [hmap]

/-! ## The length-only boundary hypothesis -/

/-- **The designated boundary word is geodesic in the relative alphabet.**
This is a statement about lengths alone: no letter is asked to lie in
`D.base`.  `Lemma44RelatorDiagramBoundary` carries it as
`boundaryWord_geodesic`, and the coercion to `RelativeReducedDiagram` discards
it. -/
def RelativeReducedDiagram.HasGeodesicBoundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R) : Prop :=
  Z.boundaryWord.length = WordMetric.wordNorm D.alphabet.carrier Z.boundary

/-- **A geodesic designated boundary has an admissible geodesic spelling.**
The spelling is letterwise, so arcs of the two words correspond. -/
theorem exists_geodesicSpelling_of_hasGeodesicBoundaryLength
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : RelativeReducedDiagram D W R)
    (hgeo : Z.HasGeodesicBoundaryLength) :
    ∃ outer : List (GGT.RelLetter G Lambda),
      GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary outer ∧
        outer.map GGT.RelLetter.val = Z.boundaryWord := by
  obtain ⟨outer, hadm, hmap⟩ :=
    exists_letterwise_spelling D Z.boundaryWord
      (fun x hx => Z.boundaryWord_isWord.letters x hx)
  refine ⟨outer, ⟨hadm, ?_, ?_⟩, hmap⟩
  · rw [one_mul, listVal_of_letterwise_spelling hmap]
    exact Z.boundaryWord_isWord.prod_eq
  · have hdist : WordMetric.wordDist D.alphabet.carrier 1 Z.boundary
        = WordMetric.wordNorm D.alphabet.carrier Z.boundary :=
      WordMetric.wordDist_one_left _ _
    rw [hdist, length_of_letterwise_spelling hmap]
    exact hgeo

/-! ## Realization at a supplied outer word -/

/-- **A planar realization of a common reduced diagram at a supplied relative
outer word.**  Every field is a field of
`GGT.VanKampen.RelativeDiscRealization` except that `outerWord_eq` names the
outer word instead of forcing the base reading. -/
structure RelativeDiscRealizationAtWord
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) {R : ℕ}
    (Z : RelativeReducedDiagram D W R)
    (outer : List (GGT.RelLetter G Lambda)) where
  diagram : DiscDiagram.{u, w, 0} W
  cellIndex : Fin Z.cells.length ≃ Fin diagram.rCellCount
  cellWord_eq : ∀ i : Fin Z.cells.length,
    (diagram.relatorCells.get (cellIndex i)).word = (Z.cells.get i).relator
  outerWord_eq : diagram.boundaryWord = outer
  reduced : diagram.Reduced

/-- The landed base-reading realization is the supplied-word realization at
the base reading, so the generalization loses nothing. -/
def relativeDiscRealizationAtWord_of_baseReading
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    (C : RelativeDiscRealization D W Z) :
    RelativeDiscRealizationAtWord D W Z
      (Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) where
  diagram := C.diagram
  cellIndex := C.cellIndex
  cellWord_eq := C.cellWord_eq
  outerWord_eq := C.outerWord_eq
  reduced := C.reduced

/-- A supplied-word realization has a positive planar relator-cell count. -/
theorem RelativeDiscRealizationAtWord.rCellCount_pos
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    {outer : List (GGT.RelLetter G Lambda)}
    (C : RelativeDiscRealizationAtWord D W Z outer) :
    0 < C.diagram.rCellCount := by
  have hcount : C.diagram.rCellCount = Z.cells.length := by
    have hcard := Fintype.card_congr C.cellIndex
    simpa only [Fintype.card_fin] using hcard.symm
  rw [hcount, Z.cells_length]
  exact Z.area_pos

/-- **The planar relator word at a cell of an `O`-equivalent diagram is the
algebraic relator of the corresponding cell**, for a supplied-word
realization. -/
theorem cellWord_eq_relator_of_oEquivalent_atWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    {outer : List (GGT.RelLetter G Lambda)}
    (hreal : RelativeDiscRealizationAtWord D W Z outer)
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

/-- **The vk residue in its supplied-word form.**  Only the outer word changes
relative to `GGT.VanKampen.RelativeDiscRealizationStatement`: it is an
arbitrary admissible relative word spelling the designated boundary, instead of
the base reading of `Z.boundaryWord`.  The cactus that proves the base-reading
form uses the outer word only through `GGT.RelLetter.listVal`. -/
def RelativeDiscRealizationSpellingStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ)
    (Z : RelativeReducedDiagram D W R)
    (outer : List (GGT.RelLetter G Lambda)),
    outer.map GGT.RelLetter.val = Z.boundaryWord →
      Nonempty (RelativeDiscRealizationAtWord D W Z outer)

/-- **The realization at a supplied spelling, proved.**  The cactus of
`GGT/VanKampen/RelativeCactus.lean` is parameterized by the outer spelling:
`cactusDiscDiagramAt` builds the planar diagram, `cellIndexEquivAt` and
`cellIndexEquivAt_word` its cell correspondence,
`cactusDiscDiagramAt_boundaryWord` its outer word, and
`cactusDiscDiagramAt_reduced` its reducedness.  The letterwise hypothesis
supplies both the length, which fixes the cactus shape, and the value.

This retires the residue: `RelativeDiscRealizationSpellingStatement` is a
theorem, not an assumption. -/
theorem relativeDiscRealizationSpellingStatement :
    RelativeDiscRealizationSpellingStatement.{u, w} := by
  intro G _ Lambda D W R Z outer hmap
  have houter : outer.length = Z.boundaryWord.length := by
    rw [← hmap, List.length_map]
  have hval : GGT.RelLetter.listVal outer = Z.boundary := by
    unfold GGT.RelLetter.listVal
    rw [hmap]
    exact Z.boundaryWord_isWord.prod_eq
  exact ⟨{
    diagram := Z.cactusDiscDiagramAt outer houter hval
    cellIndex := Z.cellIndexEquivAt outer houter hval
    cellWord_eq := Z.cellIndexEquivAt_word outer houter hval
    outerWord_eq := Z.cactusDiscDiagramAt_boundaryWord outer houter hval
    reduced := Z.cactusDiscDiagramAt_reduced outer houter hval }⟩

/-- **Model check for the vk residue.**  At the base reading it is the landed
statement, so the generalization is consistent and strictly extends what is
already proved. -/
theorem relativeDiscRealizationSpelling_baseReadingModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ)
    (Z : RelativeReducedDiagram D W R) :
    Nonempty (RelativeDiscRealizationAtWord D W Z
      (Z.boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))) := by
  obtain ⟨C⟩ := GGT.VanKampen.relativeDiscRealizationStatement D W R Z
  exact ⟨relativeDiscRealizationAtWord_of_baseReading C⟩

/-! ## The conversion residue at a supplied outer word -/

/-- **The arc-conversion residue, at a supplied letterwise spelling.**  The
planar outer word is `outer`, the algebraic boundary word is `boundaryWord`,
and `outer.map GGT.RelLetter.val = boundaryWord` matches them letter by letter,
so an arc of one is an arc of the other.  Apart from that the statement is
`RelativeExteriorArcConversionStatement`: one planar exterior region, one
algebraic boundary contiguity, an exterior arc no shorter than the planar
source arc. -/
def RelativeExteriorArcConversionAtWordStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, 0} W) (boundaryWord : List G)
    (outer : List (GGT.RelLetter G Lambda)),
    Delta.boundaryWord = outer →
    outer.map GGT.RelLetter.val = boundaryWord →
      ∀ (j : Fin Delta.rCellCount)
        (Gamma : EmbeddedBoundaryContiguity D eps Delta j)
        (relator : List (GGT.RelLetter G Lambda)),
        (GGT.VanKampen.Embedded.cell Delta j).word = relator →
          ∃ C : RelativeBoundaryContiguity D eps boundaryWord relator,
            Gamma.region.sourceArc.length ≤ C.exterior.length

/-- **Model test for the supplied-word conversion residue**, at a region whose
planar source arc is empty: the empty-exterior contiguity discharges it. -/
theorem exists_relativeBoundaryContiguity_atWord_of_sourceArc_length_zero
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

/-- Taking the letter values of a base reading recovers the original word. -/
theorem map_val_map_base
    {G : Type u} {Lambda : Type w} (l : List G) :
    (l.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)).map
        GGT.RelLetter.val = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, val_base, ih]

/-- **The supplied-word conversion residue subsumes the base-reading one**, so
adopting the spelling route costs nothing on the conversion side. -/
theorem relativeExteriorArcConversion_of_atWord
    (h : RelativeExteriorArcConversionAtWordStatement.{u, w}) :
    RelativeExteriorArcConversionStatement.{u, w} := by
  intro G _ Lambda D W eps Delta boundaryWord hbw j Gamma relator hrel
  exact h D eps Delta boundaryWord
    (boundaryWord.map (GGT.RelLetter.base : G → GGT.RelLetter G Lambda))
    hbw (map_val_map_base boundaryWord) j Gamma relator hrel

/-! ## The statement at the length-only boundary hypothesis -/

/-- **Osin's Lemma 4.4 in certificate form, at diagrams whose designated
boundary word is geodesic in the relative alphabet.**  No letter is asked to
lie in `D.base`. -/
def RelativeGreendlingerGeodesicLengthStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded →
      ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 16 →
        ∃ eps rho0 : ℕ, ∀ rho : ℕ, rho0 ≤ rho →
          ∀ (W : Set (List (GGT.RelLetter G Lambda))) (R : ℕ),
            RelWord.IsLemma44Input D W eps mu rho →
              ∀ Z : RelativeReducedDiagram D W R,
                Z.HasGeodesicBoundaryLength →
                  Nonempty (RelativeDiagramCertificate D W eps mu Z)

/-- **The main reduction, at the length-only boundary hypothesis.**  Its
hypotheses are est's three construction propositions, the vk realization at a
supplied spelling, and the supplied-word arc conversion. -/
theorem relativeGreendlingerGeodesicLengthStatement_of_components
    (hselection :
      GGT.VanKampen.EstimatingSelectionConstructionStatement.{u, w, 0})
    (hpieces :
      GGT.VanKampen.EstimatingPieceConstructionStatement.{u, w, 0})
    (hunbound :
      GGT.VanKampen.EstimatingUnboundOutputStatement.{u, w, 0})
    (hreal : RelativeDiscRealizationSpellingStatement.{u, w})
    (hconv : RelativeExteriorArcConversionAtWordStatement.{u, w}) :
    RelativeGreendlingerGeodesicLengthStatement.{u, w} := by
  intro G _ Lambda D hD mu hmu hmuUpper
  have hhyper : ∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta :=
    GGT.exists_isFourPointHyperbolic_of_isHyperbolicallyEmbedded D hD
  obtain ⟨eps, rho, hrho, hgood⟩ :=
    GGT.VanKampen.relativeGreendlingerQuasiGeodesic_of_components
      hselection hpieces hunbound D hhyper (1 / 4) 1 mu
      (by norm_num) (by norm_num) (by norm_num) hmu hmuUpper
  refine ⟨eps, rho, ?_⟩
  intro rho' hrho' W R hinput Z hgeo
  have hinput0 : RelWord.IsLemma44Input D W eps mu rho :=
    hinput.mono_parameters le_rfl le_rfl hrho'
  have hcondition :
      GGT.VanKampen.OsinCCondition D W eps mu (1 / 4) 1 rho :=
    hinput0.toOsinCCondition
  obtain ⟨outer, houter, hmap⟩ :=
    exists_geodesicSpelling_of_hasGeodesicBoundaryLength Z hgeo
  have houterVal : GGT.RelLetter.listVal outer = Z.boundary := by
    simpa using houter.2.1
  obtain ⟨Creal⟩ := hreal D W R Z outer hmap
  have hqg : IsLambdaCQuasiGeodesicWord D (1 / 4) 1 Creal.diagram.boundaryWord := by
    rw [Creal.outerWord_eq]
    exact isLambdaCQuasiGeodesicWord_of_isGeodesicWord D houter
      (by norm_num) (by norm_num)
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

/-! ## The length-only hypothesis is discharged at every Hull 4.4 diagram -/

/-- **The payoff.**  Every Hull Lemma 4.4 diagram satisfies the length-only
boundary hypothesis, with no side hypothesis at all: it is exactly the
`boundaryWord_geodesic` field that
`Lemma44OrientedRelatorDiagram.toRelativeReducedDiagram` discards.  Compare
`hasBaseGeodesicBoundary_toRelativeReducedDiagram`, which needs every boundary
letter to lie in `D.base`. -/
theorem hasGeodesicBoundaryLength_toRelativeReducedDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    (Z : Lemma44OrientedRelatorDiagram D.alphabet W R) :
    (Z.toRelativeReducedDiagram D).HasGeodesicBoundaryLength :=
  Z.boundaryWord_geodesic

/-- **The base-letter hypothesis implies the length-only one.**  So the
supplied-spelling route subsumes the base-reading route of
`HullSCRelativeGreendlingerFromComponents`. -/
theorem hasGeodesicBoundaryLength_of_hasBaseGeodesicBoundary
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {R : ℕ}
    {Z : RelativeReducedDiagram D W R}
    (h : Z.HasBaseGeodesicBoundary) :
    Z.HasGeodesicBoundaryLength := by
  have h' : GGT.OsinComponents.IsGeodesicWord D 1 Z.boundary
      (Z.boundaryWord.map
        (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)) := h
  have hlen := h'.2.2
  have hmap : (Z.boundaryWord.map
      (GGT.RelLetter.base : G → GGT.RelLetter G Lambda)).length
        = Z.boundaryWord.length := by simp
  rw [hmap, WordMetric.wordDist_one_left] at hlen
  exact hlen

end HullSC
end GroupApproximation
