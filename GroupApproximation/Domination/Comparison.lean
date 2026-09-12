import GroupApproximation.Domination.Permutation
import GroupApproximation.Domination.Unitary
import GroupApproximation.Sofic.HyperlinearNonScalar

/-!
# Permutation domination is bounded by unitary domination

The classical permutation-matrix embedding sends a finite action to an exact
finite-dimensional unitary representation.  We use the inverse permutation
matrix so that the anti-homomorphism convention for `Matrix.permMatrix`
becomes a homomorphism.  The normalized trace is exactly the fixed-point
fraction, so the squared-character defects agree without a comparison loss.

This is the scalar domination form of the standard implication "sofic implies
hyperlinear", due to Elek--Szabó in its group-approximation setting.  The new
content here is only the exact comparison of the presentation-dependent
domination predicates introduced in the companion files.
-/

namespace GroupApproximation

open Matrix

namespace FinitePermutationRepresentation

variable {G : Type*} [Group G]

/-- The exact unitary representation obtained from a finite action by inverse
permutation matrices. -/
noncomputable def toFDUnitary (ρ : FinitePermutationRepresentation G) :
    FDUnitaryRepresentation G where
  carrier := ρ.carrier
  nonempty := ρ.nonempty
  map := fun g ↦ ((ρ.map g)⁻¹).permMatrix ℂ
  map_one := by
    rw [ρ.map_one]
    simp
  map_mul := by
    intro g h
    rw [ρ.map_mul, _root_.mul_inv_rev, Matrix.permMatrix_mul]
  isUnitary := fun g ↦ permMatrix_mem_unitaryGroup ρ.carrier _

/-- Permutation-matrix normalized trace equals the fixed-point fraction. -/
theorem character_toFDUnitary (ρ : FinitePermutationRepresentation G) (g : G) :
    ρ.toFDUnitary.character g = (ρ.character g : ℂ) := by
  unfold FDUnitaryRepresentation.character toFDUnitary
  rw [normTrace_permMatrix _ _ ρ.nonempty]
  have hinv := hammingDistance_inv ρ.carrier (ρ.map g) 1
  simp only [inv_one] at hinv
  rw [hinv, ρ.character_eq_one_sub_hammingDistance]

/-- The two domination theories use exactly the same defect on a permutation
representation. -/
theorem characterDefect_toFDUnitary
    (ρ : FinitePermutationRepresentation G) (g : G) :
    ρ.toFDUnitary.characterDefect g = ρ.characterDefect g := by
  unfold FDUnitaryRepresentation.characterDefect characterDefect
  rw [character_toFDUnitary, Complex.normSq_ofReal]
  ring

end FinitePermutationRepresentation

/-- Every finite-dimensional character domination inequality restricts to
the same inequality on permutation characters.  Equivalently, whenever both
optimal constants are packaged as infima, `C_perm ≤ C_fd`. -/
theorem hasPermutationCharacterDomination_of_hasFDCharacterDomination
    {G : Type*} [Group G] {R : Finset G} {w : G}
    (h : HasFDCharacterDomination G R w) :
    HasPermutationCharacterDomination G R w := by
  obtain ⟨C, hC, hdom⟩ := h
  refine ⟨C, hC, ?_⟩
  intro ρ
  have hu := hdom ρ.toFDUnitary
  unfold fdUnitaryPowerDefectSystem PowerDefectSystem.totalDefect at hu
  unfold permutationPowerDefectSystem PowerDefectSystem.totalDefect
  simpa only [FinitePermutationRepresentation.characterDefect_toFDUnitary] using hu

/-- The corresponding qualitative implication, obtained either directly or
through the two power-linearization equivalences. -/
theorem permutationCharacterVanishesAtZero_of_fdCharacterVanishesAtZero
    {G : Type*} [Group G] {R : Finset G} {w : G}
    (h : FDCharacterVanishesAtZero G R w) :
    PermutationCharacterVanishesAtZero G R w := by
  rw [fdCharacterVanishesAtZero_iff_hasDomination] at h
  rw [permutationCharacterVanishesAtZero_iff_hasDomination]
  exact hasPermutationCharacterDomination_of_hasFDCharacterDomination h

end GroupApproximation
