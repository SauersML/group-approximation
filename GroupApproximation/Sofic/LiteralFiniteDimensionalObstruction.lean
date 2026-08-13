import GroupApproximation.Criterion.FiniteDimensionalKill
import GroupApproximation.Sofic.LiteralNonMFLinearWitness

/-!
# Finite-dimensional sterility of the literal non-MF presentation

This is the exact application of manuscript Theorem B to the literal
eight-generator group.  It uses only the displayed one-sided compression and
lamp-centralizer relations from the presentation, together with the exact
Clifford witness proving that the mark is nontrivial.  Property `(T)` is not
used.
-/

namespace GroupApproximation
namespace LiteralFiniteDimensionalObstruction

open LiteralNonMFPresentation LiteralNonMFLinearWitness

universe u

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]

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

end LiteralFiniteDimensionalObstruction
end GroupApproximation
