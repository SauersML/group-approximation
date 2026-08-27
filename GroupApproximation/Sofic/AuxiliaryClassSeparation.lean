import Mathlib.Tactic

/-!
# Auxiliary-class separation

Finite-window approximation notions often differ only in the class of
auxiliary groups permitted in a witness.  This file records the exact
logical obstruction to using the larger notion to separate two classes:
if the same action has witnesses over `C₂` but not over `C₁`, then one of
the auxiliary objects occurring in a `C₂` witness already lies outside
`C₁`.

This is a theorem about the quantifiers in the definition.  It uses no
group-approximation permanence theorem and no external mathematical input.
-/

namespace GroupApproximation

universe u v

/-- Every finite window admits an auxiliary object in `C` satisfying the
window condition `Valid`. -/
def HasWindowedAuxiliaryWitness (Window : Type u) (Auxiliary : Type v)
    (C : Auxiliary → Prop) (Valid : Window → Auxiliary → Prop) : Prop :=
  ∀ window, ∃ auxiliary, C auxiliary ∧ Valid window auxiliary

/-- If `C₂` supplies witnesses but `C₁` does not, a failed `C₁` window has
a `C₂` witness whose auxiliary object is not in `C₁`. -/
theorem exists_auxiliary_witness_outside_of_separation
    {Window : Type u} {Auxiliary : Type v}
    {C₁ C₂ : Auxiliary → Prop} {Valid : Window → Auxiliary → Prop}
    (h₂ : HasWindowedAuxiliaryWitness Window Auxiliary C₂ Valid)
    (h₁ : ¬HasWindowedAuxiliaryWitness Window Auxiliary C₁ Valid) :
    ∃ window auxiliary,
      C₂ auxiliary ∧ Valid window auxiliary ∧ ¬C₁ auxiliary := by
  classical
  simp only [HasWindowedAuxiliaryWitness] at h₂ h₁
  push Not at h₁
  obtain ⟨window, hwindow⟩ := h₁
  obtain ⟨auxiliary, hC₂, hvalid⟩ := h₂ window
  refine ⟨window, auxiliary, hC₂, hvalid, ?_⟩
  intro hC₁
  exact hwindow auxiliary hC₁ hvalid

/-- Class-level form: a strict separation between two witness notions
already certifies that the permitted auxiliary classes are distinct. -/
theorem exists_auxiliary_outside_of_windowed_separation
    {Window : Type u} {Auxiliary : Type v}
    {C₁ C₂ : Auxiliary → Prop} {Valid : Window → Auxiliary → Prop}
    (h₂ : HasWindowedAuxiliaryWitness Window Auxiliary C₂ Valid)
    (h₁ : ¬HasWindowedAuxiliaryWitness Window Auxiliary C₁ Valid) :
    ∃ auxiliary, C₂ auxiliary ∧ ¬C₁ auxiliary := by
  obtain ⟨_window, auxiliary, hC₂, _hvalid, hC₁⟩ :=
    exists_auxiliary_witness_outside_of_separation h₂ h₁
  exact ⟨auxiliary, hC₂, hC₁⟩

end GroupApproximation
