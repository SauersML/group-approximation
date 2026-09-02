import GroupApproximation.GGT.VanKampen.Estimating.Partition
import GroupApproximation.GGT.HullSCPublishedSmallCancellation
import GroupApproximation.GGT.HullSCRelativeGreendlingerStatement
import GroupApproximation.GGT.OsinTheorem54SepPolygon
import Mathlib.Tactic

/-!
# Relative Greendlinger with the source boundary hypothesis

This file states Osin Lemma Gr0 with its `(lambda,c)`-quasi-geodesic outer
boundary and proves its strict `> 1 - 13 * mu` conclusion from embedded
estimating-system data.  Embedded contiguity regions are finite G-cell face
sets in the ambient disc diagram, so this module does not import the separate
`ContiguityRegion` development.

The construction statement at the end is the geometric output of Appendix
Definition M, Lemmas 61, 62, 65(a), and Lemma Eul.  All weighted summation and
selection of the large exterior cell are proved here.  The old Hull statement
is retained only as a named alias; its consumers must supply a quasi-geodesic
boundary and a bridge from a cyclic embedded arc to their based certificate.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

open GroupApproximation.HullSC
open GroupApproximation.WordMetric

universe u w v

/-! ## Exact source hypotheses -/

/-- A word labels a `(lambda,c)`-quasi-geodesic path in the relative Cayley
graph.  This is Osin's convention with `0 < lambda <= 1`. -/
def IsLambdaCQuasiGeodesicWord
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (lambda c : ℝ)
    (word : List (GGT.RelLetter G Lambda)) : Prop :=
  RelWord.IsAdmissible D word ∧
    ∀ i j : ℕ, i ≤ j → j ≤ word.length →
      lambda * ((j - i : ℕ) : ℝ) - c ≤
        ((wordDist D.alphabet.carrier
          (GGT.OsinComponents.vertex 1 word i)
          (GGT.OsinComponents.vertex 1 word j) : ℕ) : ℝ)

/-- The empty path is `(lambda,c)`-quasi-geodesic for every nonnegative
additive constant. -/
theorem isLambdaCQuasiGeodesicWord_nil
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (lambda c : ℝ) (hc : 0 ≤ c) :
    IsLambdaCQuasiGeodesicWord D lambda c [] := by
  refine ⟨by simp [RelWord.IsAdmissible], ?_⟩
  intro i j hij hj
  have hj0 : j = 0 := by simpa using hj
  have hi0 : i = 0 := by omega
  subst i
  subst j
  change lambda * (((0 - 0 : ℕ) : ℝ)) - c ≤
    ((wordDist D.alphabet.carrier
      (GGT.OsinComponents.vertex 1
        ([] : List (GGT.RelLetter G Lambda)) 0)
      (GGT.OsinComponents.vertex 1
        ([] : List (GGT.RelLetter G Lambda)) 0) : ℕ) : ℝ)
  have hdist : (0 : ℝ) ≤
      ((wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex 1
          ([] : List (GGT.RelLetter G Lambda)) 0)
        (GGT.OsinComponents.vertex 1
          ([] : List (GGT.RelLetter G Lambda)) 0) : ℕ) : ℝ) := by positivity
  rw [show (((0 - 0 : ℕ) : ℝ)) = 0 by norm_num, mul_zero]
  exact le_trans (sub_nonpos.mpr hc) hdist

/-- Osin's `C(epsilon,mu,lambda,c,rho)` condition. -/
structure OsinCCondition
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps : ℕ) (mu lambda c : ℝ) (rho : ℕ) : Prop extends
    RelWord.IsSmallCancellation D W eps mu rho where
  quasiGeodesic : ∀ word ∈ W,
    IsLambdaCQuasiGeodesicWord D lambda c word
  publishedPiecesSmall : ∀ first second word,
    RelWord.IsPublishedPiece D W eps first second word →
      max (first.length : ℝ) (second.length : ℝ) < mu * word.length

/-- The empty symmetrized family satisfies the exact Osin condition. -/
theorem osinCCondition_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps rho : ℕ) (mu lambda c : ℝ) :
    OsinCCondition D (∅ : Set (List (GGT.RelLetter G Lambda)))
      eps mu lambda c rho := by
  refine {
    admissible := ?_
    inv_mem := ?_
    rotate_mem := ?_
    long := ?_
    deep := ?_
    pieces_small := ?_
    quasiGeodesic := ?_
    publishedPiecesSmall := ?_ }
  · intro word hword
    exact hword.elim
  · intro word hword
    exact hword.elim
  · intro word hword
    exact hword.elim
  · intro word hword
    exact hword.elim
  · intro word hword
    exact hword.elim
  · intro first word hpiece
    exact hpiece.1.elim
  · intro word hword
    exact hword.elim
  · intro first second word hpiece
    exact hpiece.1.elim

/-! ## Embedded `O`-equivalence and exterior witnesses -/

/-- A G-cell-only replacement keeps the outer word and gives a bijection of
relator cells preserving their labels. -/
structure OEquivalentDiscDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta Delta' : DiscDiagram.{u, w, v} W) where
  boundaryWord_eq : Delta'.boundaryWord = Delta.boundaryWord
  cellIndex : Fin Delta.rCellCount ≃ Fin Delta'.rCellCount
  cellWord_eq : ∀ i : Fin Delta.rCellCount,
    (Embedded.cell Delta' (cellIndex i)).word = (Embedded.cell Delta i).word

/-- `O`-equivalence is reflexive. -/
def OEquivalentDiscDiagram.refl
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (Delta : DiscDiagram.{u, w, v} W) : OEquivalentDiscDiagram Delta Delta where
  boundaryWord_eq := rfl
  cellIndex := Equiv.refl _
  cellWord_eq := fun _ => rfl

namespace OEquivalentDiscDiagram

/-- An `O`-equivalence preserves the number of relator cells. -/
theorem rCellCount_eq
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {Delta Delta' : DiscDiagram.{u, w, v} W}
    (equiv : OEquivalentDiscDiagram Delta Delta') :
    Delta'.rCellCount = Delta.rCellCount := by
  have hcard := Fintype.card_congr equiv.cellIndex
  simpa only [Fintype.card_fin] using hcard.symm

/-- A quasi-geodesic boundary word transports across an `O`-equivalence. -/
theorem boundary_quasiGeodesic
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda}
    {Delta Delta' : DiscDiagram.{u, w, v} W}
    {lambda c : ℝ}
    (equiv : OEquivalentDiscDiagram Delta Delta')
    (hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord) :
    IsLambdaCQuasiGeodesicWord D lambda c Delta'.boundaryWord := by
  rw [equiv.boundaryWord_eq]
  exact hboundary

end OEquivalentDiscDiagram

/-- One selected embedded region from cell `i` to the outer boundary. -/
structure EmbeddedBoundaryContiguity
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (Delta : DiscDiagram.{u, w, v} W)
    (i : Fin Delta.rCellCount) where
  faces : Finset Delta.toCombMap.Face
  region : Embedded.Contiguity D eps Delta faces
  source_eq : region.source = i
  target_eq : region.target = none

namespace EmbeddedBoundaryContiguity

/-- Length of the relator-cell contiguity arc. -/
def weight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount}
    (contiguity : EmbeddedBoundaryContiguity D eps Delta i) : ℝ :=
  contiguity.region.sourceArc.length

end EmbeddedBoundaryContiguity

/-! ## The embedded estimating-system count -/

/-- Geometric output of the distinguished embedded family after Lemma 65(a).
The canonical partition supplies the three cellwise weights.  The construction
also identifies the complete exterior class at each cell with at most one
boundary region, as established in Lemma 65(b). -/
structure EmbeddedEstimatingSystem
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    (eps : ℕ) (mu : ℝ) (Delta : DiscDiagram.{u, w, v} W) where
  selected : EstimatingSelection.DistinguishedFamily
    (Embedded.Compatible (D := D) (eps := eps) (Delta := Delta))
    (Embedded.Candidate.weight (D := D) (eps := eps) (Delta := Delta))
  partition : Embedded.DiagramBoundaryPartition selected.family
  outer : ∀ i : Fin Delta.rCellCount,
    Option (EmbeddedBoundaryContiguity D eps Delta i)
  outerWeight_eq : ∀ i : Fin Delta.rCellCount,
    (match outer i with
      | none => 0
      | some contiguity => contiguity.weight) =
        partition.kindWeight Embedded.CellArcKind.exterior i
  totalWeight_pos :
    0 < ∑ i : Fin Delta.rCellCount,
      ((Embedded.cell Delta i).word.length : ℝ)
  interior_total_le :
    (∑ i : Fin Delta.rCellCount,
        partition.kindWeight Embedded.CellArcKind.interior i) ≤
      10 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ)
  uncovered_total_le :
    (∑ i : Fin Delta.rCellCount,
        partition.kindWeight Embedded.CellArcKind.unbound i) ≤
      2 * mu * ∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ)

namespace EmbeddedEstimatingSystem

/-- Exterior weight selected at one relator cell. -/
def outerWeight
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    (system : EmbeddedEstimatingSystem D eps mu Delta)
    (i : Fin Delta.rCellCount) : ℝ :=
  match system.outer i with
  | none => 0
  | some contiguity => contiguity.weight

/-- The positioned classification partitions total relator perimeter. -/
theorem total_partition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    (system : EmbeddedEstimatingSystem D eps mu Delta) :
    (∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ)) =
      (∑ i : Fin Delta.rCellCount, system.outerWeight i) +
      (∑ i : Fin Delta.rCellCount,
        system.partition.kindWeight Embedded.CellArcKind.interior i) +
      (∑ i : Fin Delta.rCellCount,
        system.partition.kindWeight Embedded.CellArcKind.unbound i) := by
  calc
    (∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ)) =
        ∑ i : Fin Delta.rCellCount,
          (system.partition.kindWeight Embedded.CellArcKind.exterior i +
            system.partition.kindWeight Embedded.CellArcKind.interior i +
            system.partition.kindWeight Embedded.CellArcKind.unbound i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact system.partition.cellWeight_partition i
    _ = (∑ i : Fin Delta.rCellCount,
          system.partition.kindWeight Embedded.CellArcKind.exterior i) +
        (∑ i : Fin Delta.rCellCount,
          system.partition.kindWeight Embedded.CellArcKind.interior i) +
        (∑ i : Fin Delta.rCellCount,
          system.partition.kindWeight Embedded.CellArcKind.unbound i) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by
      apply congrArg₂ (fun exterior interior : ℝ => exterior + interior +
        ∑ i : Fin Delta.rCellCount,
          system.partition.kindWeight Embedded.CellArcKind.unbound i)
      · apply Finset.sum_congr rfl
        intro i _
        exact system.outerWeight_eq i |>.symm
      · rfl

/-- The two global budgets leave strictly more than `1 - 13 * mu` on
exterior arcs. -/
theorem total_exterior_gt
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    (hmu : 0 < mu) (system : EmbeddedEstimatingSystem D eps mu Delta) :
    (1 - 13 * mu) *
        (∑ i : Fin Delta.rCellCount,
          ((Embedded.cell Delta i).word.length : ℝ)) <
      ∑ i : Fin Delta.rCellCount, system.outerWeight i := by
  have hpartition := system.total_partition
  have hslack : 0 < mu *
      (∑ i : Fin Delta.rCellCount,
        ((Embedded.cell Delta i).word.length : ℝ)) :=
    mul_pos hmu system.totalWeight_pos
  linarith [system.interior_total_le, system.uncovered_total_le]

/-- Some cell has one embedded exterior region of strict degree greater than
`1 - 13 * mu`. -/
theorem exists_large_exterior
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps : ℕ} {mu : ℝ} {Delta : DiscDiagram.{u, w, v} W}
    (hmu : 0 < mu) (hmuUpper : mu ≤ 1 / 16)
    (system : EmbeddedEstimatingSystem D eps mu Delta) :
    ∃ (i : Fin Delta.rCellCount)
      (contiguity : EmbeddedBoundaryContiguity D eps Delta i),
      system.outer i = some contiguity ∧
        (1 - 13 * mu) *
            ((Embedded.cell Delta i).word.length : ℝ) < contiguity.weight := by
  have htotal := system.total_exterior_gt hmu
  have hindex : ∃ i : Fin Delta.rCellCount,
      (1 - 13 * mu) * ((Embedded.cell Delta i).word.length : ℝ) <
        system.outerWeight i := by
    by_contra hnone
    have hall : ∀ i : Fin Delta.rCellCount,
        system.outerWeight i ≤
          (1 - 13 * mu) * ((Embedded.cell Delta i).word.length : ℝ) := by
      intro i
      exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hall i
    rw [← Finset.mul_sum] at hsum
    linarith
  obtain ⟨i, hi⟩ := hindex
  have hcoefficient : 0 ≤ 1 - 13 * mu := by linarith
  cases houter : system.outer i with
  | none =>
      rw [outerWeight, houter] at hi
      have hperimeter : 0 ≤ ((Embedded.cell Delta i).word.length : ℝ) := by positivity
      have := mul_nonneg hcoefficient hperimeter
      linarith
  | some contiguity =>
      refine ⟨i, contiguity, houter, ?_⟩
      rwa [outerWeight, houter] at hi

end EmbeddedEstimatingSystem

/-! ## Source statement and its geometric construction frontier -/

/-- Source-faithful Osin Lemma Gr0. -/
def RelativeGreendlingerQuasiGeodesicStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    (∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
      ∀ lambda c mu : ℝ,
        0 < lambda → lambda ≤ 1 → 0 ≤ c →
        0 < mu → mu ≤ 1 / 16 →
          ∃ eps rho : ℕ, 0 < rho ∧
            ∀ (W : Set (List (GGT.RelLetter G Lambda))),
              OsinCCondition D W eps mu lambda c rho →
                ∀ Delta : DiscDiagram.{u, w, v} W,
                  Delta.Reduced → 0 < Delta.rCellCount →
                  IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
                    ∃ Delta' : DiscDiagram.{u, w, v} W,
                      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
                        ∃ (faces : Finset Delta'.toCombMap.Face)
                          (Gamma : Embedded.Contiguity D eps Delta' faces),
                          Gamma.target = none ∧
                            (1 - 13 * mu) *
                                ((Embedded.cell Delta' Gamma.source).word.length : ℝ) <
                              (Gamma.sourceArc.length : ℝ)

/-- The strictly smaller geometric construction used by the numerical Gr0
count: produce an embedded estimating system after an `O`-equivalent
G-cell-only replacement. -/
def EmbeddedEstimatingSystemConstructionStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    (∃ delta : ℕ,
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta) →
      ∀ lambda c mu : ℝ,
        0 < lambda → lambda ≤ 1 → 0 ≤ c →
        0 < mu → mu ≤ 1 / 16 →
          ∃ eps rho : ℕ, 0 < rho ∧
            ∀ (W : Set (List (GGT.RelLetter G Lambda))),
              OsinCCondition D W eps mu lambda c rho →
                ∀ Delta : DiscDiagram.{u, w, v} W,
                  Delta.Reduced → 0 < Delta.rCellCount →
                  IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord →
                    ∃ Delta' : DiscDiagram.{u, w, v} W,
                      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
                        Nonempty (EmbeddedEstimatingSystem D eps mu Delta')

/-- The embedded construction implies the exact strict source conclusion. -/
theorem relativeGreendlingerQuasiGeodesic
    (hconstruction : EmbeddedEstimatingSystemConstructionStatement.{u, w, v}) :
    RelativeGreendlingerQuasiGeodesicStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda hlambdaUpper hc hmu hmuUpper
  obtain ⟨eps, rho, hrho, hsystems⟩ := hconstruction D hhyper lambda c mu
    hlambda hlambdaUpper hc hmu hmuUpper
  refine ⟨eps, rho, hrho, ?_⟩
  intro W hcondition Delta hred hcells hboundary
  obtain ⟨Delta', hequiv, system⟩ :=
    hsystems W hcondition Delta hred hcells hboundary
  obtain ⟨system⟩ := system
  obtain ⟨i, contiguity, _, hlarge⟩ :=
    system.exists_large_exterior hmu hmuUpper
  refine ⟨Delta', hequiv, contiguity.faces, contiguity.region,
    contiguity.target_eq, ?_⟩
  have hlength :
      ((Embedded.cell Delta' contiguity.region.source).word.length : ℝ) =
        ((Embedded.cell Delta' i).word.length : ℝ) := by
    rw [contiguity.source_eq]
  rw [hlength]
  simpa only [EmbeddedBoundaryContiguity.weight] using hlarge

/-- The construction frontier is correctly vacuous over the empty family:
there is no positive-cell diagram to which it could apply. -/
theorem embeddedEstimatingSystemConstruction_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (_D : GGT.RelGenSet G Lambda)
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda))))
    (hcells : 0 < Delta.rCellCount) : False := by
  have hnil : Delta.relatorCells = [] := by
    cases hcellsList : Delta.relatorCells with
    | nil => rfl
    | cons cell cells =>
        have hmem : cell ∈ Delta.relatorCells := by rw [hcellsList]; simp
        exact cell.word_mem.elim
  rw [DiscDiagram.rCellCount, hnil, List.length_nil] at hcells
  omega

/-! The source-faithful statement has the expected empty-family model. -/

/-- In the empty relator family, the positive-cell branch of the
quasi-geodesic Gr0 conclusion is impossible. -/
theorem relativeGreendlingerQuasiGeodesic_emptyFamilyModel
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (eps _rho : ℕ) (lambda c mu : ℝ)
    (Delta : DiscDiagram.{u, w, v}
      (∅ : Set (List (GGT.RelLetter G Lambda))))
    (_hred : Delta.Reduced) (hcells : 0 < Delta.rCellCount)
    (_hboundary : IsLambdaCQuasiGeodesicWord D lambda c Delta.boundaryWord) :
    ∃ Delta' : DiscDiagram.{u, w, v}
        (∅ : Set (List (GGT.RelLetter G Lambda))),
      Nonempty (OEquivalentDiscDiagram Delta Delta') ∧
        ∃ (faces : Finset Delta'.toCombMap.Face)
          (Gamma : Embedded.Contiguity D eps Delta' faces),
          Gamma.target = none ∧
            (1 - 13 * mu) *
                ((Embedded.cell Delta' Gamma.source).word.length : ℝ) <
              (Gamma.sourceArc.length : ℝ) := by
  exact (embeddedEstimatingSystemConstruction_emptyFamilyModel D Delta hcells).elim

/-! ## Legacy consumer alias -/

/-- The old Hull statement omits the quasi-geodesic boundary hypothesis.  It
is retained as a type alias only; a consumer can derive it after choosing
quasi-geodesic representatives and bridging cyclic embedded arcs to its based
certificate. -/
def RelativeGreendlingerStatement : Prop :=
  HullSC.RelativeGreendlingerStatement.{u, w}

end VanKampen
end GGT
end GroupApproximation
