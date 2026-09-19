import GroupApproximation.Criterion.FiniteDimensionalKill
import GroupApproximation.Sofic.LiteralNonMFLinearWitness
import Mathlib.RepresentationTheory.Basic

/-!
# Finite-dimensional sterility of the literal marked presentation

This is the exact application of manuscript Theorem B to the literal
eight-generator group.  It uses only the displayed one-sided compression and
lamp-centralizer relations from the presentation, together with the exact
Clifford witness proving that the mark is nontrivial.  Property `(T)` is not
used.
-/

namespace GroupApproximation
namespace LiteralFiniteDimensionalObstruction

open LiteralNonMFPresentation LiteralNonMFLinearWitness

universe u v

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/-- Every finite-dimensional linear representation of the literal group
kills its designated marked word (the literal-group instance of manuscript
Theorem B). -/
theorem map_literal_mark_eq_one [FiniteDimensional k V]
    (π : MarkedGroup →* (Module.End k V)ˣ) : π mark = 1 := by
  let Γ : Set MarkedGroup := baseMap.range
  have ha : baseMap (PresentedGroup.of v1Index) ∈ Γ :=
    ⟨PresentedGroup.of v1Index, rfl⟩
  have hcomp : ∀ γ ∈ Γ, stable * γ * stable⁻¹ ∈ Γ := by
    intro γ hγ
    rcases hγ with ⟨g, rfl⟩
    exact stable_conjugates_base_into_base g
  have hcen : ∀ γ ∈ Γ, lamp * γ = γ * lamp := by
    intro γ hγ
    rcases hγ with ⟨g, rfl⟩
    exact (lamp_commutes_base g).eq
  rw [mark_eq_markedCompressionWord, markedCompressionWord]
  exact map_marked_commutator_eq_one_units π ha hcomp hcen

/-- No finite-dimensional linear representation of the literal group is
faithful: every such representation identifies the nontrivial mark with the
identity (the group-level assertion in manuscript Corollary `cor:notRFD`). -/
theorem literal_finiteDimensional_rep_not_injective
    [FiniteDimensional k V]
    (π : MarkedGroup →* (Module.End k V)ˣ) :
    ¬ Function.Injective π := by
  intro hπ
  apply literal_mark_ne_one
  apply hπ
  rw [map_literal_mark_eq_one π, map_one]

/-- Every homomorphism from the literal group to a finite group kills the
marked element.  We apply the finite-dimensional theorem to the faithful left
regular representation of the target over `ℚ`. -/
theorem map_literal_mark_eq_one_of_finite
    {Q : Type*} [Group Q] [Finite Q] (φ : MarkedGroup →* Q) :
    φ mark = 1 := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  let regularUnits := (Representation.leftRegular ℚ Q).toHomUnits
  have hkill := map_literal_mark_eq_one (regularUnits.comp φ)
  have hmaps := congrArg Units.val hkill
  have hatOne := congrArg
    (fun f ↦ f (MonoidAlgebra.single (1 : Q) (1 : ℚ))) hmaps
  apply MonoidAlgebra.of_injective (R := ℚ)
  simpa [regularUnits] using hatOne

/-- The literal mark has no detector in any finite quotient.  Since the mark
is nontrivial, this is the precise marked-element failure of residual
finiteness asserted in manuscript Corollary `cor:notRFD`. -/
theorem no_finite_quotient_detects_literal_mark :
    ¬ ∃ (Q : Type) (_ : Group Q) (_ : Finite Q)
        (φ : MarkedGroup →* Q), φ mark ≠ 1 := by
  rintro ⟨Q, _, _, φ, hφ⟩
  exact hφ (map_literal_mark_eq_one_of_finite φ)

/-- Exact outer-form package for the manuscript's non-RFD corollary. -/
theorem manuscriptFiniteDimensionalConsequences :
    (∀ {K : Type u} {W : Type v} [Field K] [AddCommGroup W]
        [Module K W] [FiniteDimensional K W]
        (π : MarkedGroup →* (Module.End K W)ˣ),
          ¬ Function.Injective π) ∧
      (∀ {K : Type u} {W : Type v} [Field K] [AddCommGroup W]
        [Module K W] [FiniteDimensional K W]
        (π : MarkedGroup →* (Module.End K W)ˣ), π mark = 1) ∧
      (∀ {Q : Type*} [Group Q] [Finite Q] (φ : MarkedGroup →* Q),
        φ mark = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K W _ _ _ _ π
    exact literal_finiteDimensional_rep_not_injective π
  · intro K W _ _ _ _ π
    exact map_literal_mark_eq_one π
  · intro Q _ _ φ
    exact map_literal_mark_eq_one_of_finite φ

end LiteralFiniteDimensionalObstruction
end GroupApproximation
