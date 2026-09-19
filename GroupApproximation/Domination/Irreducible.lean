import GroupApproximation.Domination.Affine
import Mathlib.RepresentationTheory.Irreducible

/-!
# Irreducible block domination

This file gives a representation-theoretic name to the blocks in
`AffineBlockDecomposition` and proves the uniform bounded-degree theorem once
fixed-dimensional irreducible bounds are available.

Finite-dimensional unitary complete reducibility is classical: invariant
subspaces have invariant orthogonal complements.  Constructing the actual
decomposition is deliberately kept separate from the weighted domination
argument below, so the external representation-theory input remains visible.
-/

namespace GroupApproximation

open scoped BigOperators

namespace FDUnitaryRepresentation

variable {G : Type*} [Group G]

/-- The ordinary linear representation underlying a bundled unitary matrix
representation. -/
noncomputable def toRepresentation (π : FDUnitaryRepresentation G) :
    Representation ℂ G (π.carrier → ℂ) :=
  (Units.coeHom (Module.End ℂ (π.carrier → ℂ))).comp
    ((Matrix.UnitaryGroup.embeddingGL (n := π.carrier) (α := ℂ)).comp
      π.toUnitaryHom)

/-- Irreducibility in the standard sense of having no proper nonzero
subrepresentation. -/
abbrev IsIrreducible (π : FDUnitaryRepresentation G) : Prop :=
  Representation.IsIrreducible π.toRepresentation

end FDUnitaryRepresentation

variable (G : Type*) [Group G]

/-- Affine domination restricted to irreducible representations of one
dimension. -/
def HasIrreducibleAffineDominationInDimension
    (d : ℕ) (R : Finset G) (w : G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ π : FDUnitaryRepresentation G,
    π.IsIrreducible → Fintype.card π.carrier = d →
      π.affineCharacterDefect w ≤
        C * ∑ r ∈ R, π.affineCharacterDefect r

/-- One affine domination constant over all finite-dimensional irreducible
unitary representations. -/
def HasIrreducibleAffineDomination (R : Finset G) (w : G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ π : FDUnitaryRepresentation G,
    π.IsIrreducible →
      π.affineCharacterDefect w ≤
        C * ∑ r ∈ R, π.affineCharacterDefect r

/-- One affine domination constant for irreducibles of degree at most `D`. -/
def HasIrreducibleAffineDominationUpToDimension
    (D : ℕ) (R : Finset G) (w : G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ π : FDUnitaryRepresentation G,
    π.IsIrreducible → Fintype.card π.carrier ≤ D →
      π.affineCharacterDefect w ≤
        C * ∑ r ∈ R, π.affineCharacterDefect r

/-- A sequence of irreducibles violating domination at every fixed linear
scale. -/
def IsIrreducibleAffineEscapingSequence
    (R : Finset G) (w : G) (π : ℕ → FDUnitaryRepresentation G) : Prop :=
  (∀ n, (π n).IsIrreducible) ∧
  ∀ C : ℝ, 0 ≤ C → ∃ N : ℕ, ∀ n ≥ N,
    C * ∑ r ∈ R, (π n).affineCharacterDefect r <
      (π n).affineCharacterDefect w

/-- Finitely many fixed irreducible-degree constants combine into one
bounded-degree constant. -/
theorem hasIrreducibleAffineDominationUpToDimension_of_each
    {D : ℕ} {R : Finset G} {w : G}
    (hfixed : ∀ d ≤ D,
      HasIrreducibleAffineDominationInDimension G d R w) :
    HasIrreducibleAffineDominationUpToDimension G D R w := by
  classical
  let C : ℕ → ℝ := fun d ↦ if hd : d ≤ D then Classical.choose (hfixed d hd) else 0
  have hC : ∀ d ≤ D, 0 ≤ C d := by
    intro d hd
    simp only [C, dif_pos hd]
    exact (Classical.choose_spec (hfixed d hd)).1
  have hdom : ∀ d, (hd : d ≤ D) → ∀ π : FDUnitaryRepresentation G,
      π.IsIrreducible → Fintype.card π.carrier = d →
        π.affineCharacterDefect w ≤
          C d * ∑ r ∈ R, π.affineCharacterDefect r := by
    intro d hd π hirr hπ
    simp only [C, dif_pos hd]
    exact (Classical.choose_spec (hfixed d hd)).2 π hirr hπ
  let Cmax : ℝ := ∑ d ∈ Finset.range (D + 1), C d
  have hCmax : 0 ≤ Cmax := by
    unfold Cmax
    exact Finset.sum_nonneg fun d hd ↦ hC d
      (Nat.le_of_lt_succ (Finset.mem_range.mp hd))
  refine ⟨Cmax, hCmax, ?_⟩
  intro π hirr hdim
  let d := Fintype.card π.carrier
  have hd : d ≤ D := hdim
  have hdmem : d ∈ Finset.range (D + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hCd : C d ≤ Cmax := by
    unfold Cmax
    exact Finset.single_le_sum
      (fun i hi ↦ hC i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) hdmem
  exact (hdom d hd π hirr rfl).trans
    (mul_le_mul_of_nonneg_right hCd
      (Finset.sum_nonneg fun r _ ↦ π.affineCharacterDefect_nonneg r))

/-- Failure of global irreducible domination supplies a sequence bad at every
linear scale. -/
theorem exists_irreducibleAffineEscapingSequence
    {R : Finset G} {w : G}
    (hglobal : ¬ HasIrreducibleAffineDomination G R w) :
    ∃ π : ℕ → FDUnitaryRepresentation G,
      IsIrreducibleAffineEscapingSequence G R w π := by
  have hbad : ∀ n : ℕ, ∃ π : FDUnitaryRepresentation G,
      π.IsIrreducible ∧
      (n : ℝ) * ∑ r ∈ R, π.affineCharacterDefect r <
        π.affineCharacterDefect w := by
    intro n
    by_contra hn
    apply hglobal
    refine ⟨n, Nat.cast_nonneg n, ?_⟩
    intro π hirr
    have hnot := not_exists.mp hn π
    exact le_of_not_gt (fun hgt ↦ hnot ⟨hirr, hgt⟩)
  choose π hirr hπ using hbad
  refine ⟨π, hirr, ?_⟩
  intro C hC
  obtain ⟨N, hN⟩ := exists_nat_ge C
  refine ⟨N, fun n hn ↦ ?_⟩
  have hCn : C ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have htotal : 0 ≤ ∑ r ∈ R, (π n).affineCharacterDefect r :=
    Finset.sum_nonneg fun r _ ↦ (π n).affineCharacterDefect_nonneg r
  exact (mul_le_mul_of_nonneg_right hCn htotal).trans_lt (hπ n)

/-- **Irreducible dimension escape.**  If each fixed irreducible dimension is
controlled but global irreducible domination fails, there is a bad sequence
whose irreducible degrees tend to infinity. -/
theorem obstruction_requires_irreducibleDimensionEscape
    {R : Finset G} {w : G}
    (hfixed : ∀ d,
      HasIrreducibleAffineDominationInDimension G d R w)
    (hglobal : ¬ HasIrreducibleAffineDomination G R w) :
    ∃ π : ℕ → FDUnitaryRepresentation G,
      IsIrreducibleAffineEscapingSequence G R w π ∧
      Filter.Tendsto (fun n ↦ Fintype.card (π n).carrier)
        Filter.atTop Filter.atTop := by
  obtain ⟨π, hπ⟩ := exists_irreducibleAffineEscapingSequence G hglobal
  refine ⟨π, hπ, Filter.tendsto_atTop.2 ?_⟩
  intro D
  have hup : HasIrreducibleAffineDominationUpToDimension G D R w :=
    hasIrreducibleAffineDominationUpToDimension_of_each G
      (fun d _ ↦ hfixed d)
  obtain ⟨C, hC, hdom⟩ := hup
  obtain ⟨N, hN⟩ := hπ.2 C hC
  refine Filter.eventually_atTop.2 ⟨N, fun n hn ↦ ?_⟩
  by_contra hnot
  have hdim : Fintype.card (π n).carrier ≤ D :=
    Nat.le_of_lt (Nat.lt_of_not_ge hnot)
  exact (not_lt_of_ge (hdom (π n) (hπ.1 n) hdim)) (hN n hn)

/-- A block decomposition all of whose blocks are irreducible. -/
structure IrreducibleAffineBlockDecomposition
    (π : FDUnitaryRepresentation G) extends AffineBlockDecomposition G π where
  irreducible : ∀ j, (toAffineBlockDecomposition.representation j).IsIrreducible

/-- One affine domination constant for every representation supplied with an
irreducible decomposition whose block degrees are at most `D`.  Total
dimension and block multiplicities are unrestricted. -/
def HasBoundedIrreducibleDegreeAffineDomination
    (D : ℕ) (R : Finset G) (w : G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (π : FDUnitaryRepresentation G)
      (B : IrreducibleAffineBlockDecomposition G π),
    B.toAffineBlockDecomposition.DegreeBounded G D →
      π.affineCharacterDefect w ≤
        C * ∑ r ∈ R, π.affineCharacterDefect r

/-- **Bounded irreducible degree is harmless.**  Fixed-dimensional bounds on
irreducibles combine into one constant for arbitrary sums and arbitrary
multiplicities of irreducibles of degree at most `D`. -/
theorem boundedIrreducibleDegree_affineDomination
    {D : ℕ} {R : Finset G} {w : G}
    (hfixed : ∀ d ≤ D,
      HasIrreducibleAffineDominationInDimension G d R w) :
    HasBoundedIrreducibleDegreeAffineDomination G D R w := by
  classical
  let C : ℕ → ℝ := fun d ↦ if hd : d ≤ D then Classical.choose (hfixed d hd) else 0
  have hC : ∀ d ≤ D, 0 ≤ C d := by
    intro d hd
    simp only [C, dif_pos hd]
    exact (Classical.choose_spec (hfixed d hd)).1
  have hdom : ∀ d, (hd : d ≤ D) → ∀ π : FDUnitaryRepresentation G,
      π.IsIrreducible → Fintype.card π.carrier = d →
        π.affineCharacterDefect w ≤
          C d * ∑ r ∈ R, π.affineCharacterDefect r := by
    intro d hd π hirr hπ
    simp only [C, dif_pos hd]
    exact (Classical.choose_spec (hfixed d hd)).2 π hirr hπ
  let Cmax : ℝ := ∑ d ∈ Finset.range (D + 1), C d
  have hCmax : 0 ≤ Cmax := by
    unfold Cmax
    exact Finset.sum_nonneg fun d hd ↦ hC d
      (Nat.le_of_lt_succ (Finset.mem_range.mp hd))
  refine ⟨Cmax, hCmax, ?_⟩
  intro π B hdegree
  apply affineDomination_of_blockwise G π B.toAffineBlockDecomposition Cmax
  intro j
  let d := Fintype.card (B.toAffineBlockDecomposition.representation j).carrier
  have hd : d ≤ D := hdegree j
  have hdmem : d ∈ Finset.range (D + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hd)
  have hCd : C d ≤ Cmax := by
    unfold Cmax
    exact Finset.single_le_sum
      (fun i hi ↦ hC i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) hdmem
  exact (hdom d hd _ (B.irreducible j) rfl).trans
    (mul_le_mul_of_nonneg_right hCd
      (Finset.sum_nonneg fun r _ ↦
        (B.toAffineBlockDecomposition.representation j).affineCharacterDefect_nonneg r))

end GroupApproximation
