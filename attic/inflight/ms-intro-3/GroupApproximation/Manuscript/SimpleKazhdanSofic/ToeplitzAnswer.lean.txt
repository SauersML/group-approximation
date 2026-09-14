import GroupApproximation.Manuscript.SimpleKazhdanSofic.MainAssembly
import GroupApproximation.Pestov91.SubshiftMinimal
import GroupApproximation.Pestov91.WitnessAssembly
import GroupApproximation.Meta.AxiomGuard

/-!
# The Toeplitz subshift, and the answer to the questions of Brown, Ozawa and Pestov

`simple_kazhdan_sofic_group.tex` (origin/main tip), abstract and introduction:

> This answers the question of Brown and Ozawa whether an infinite simple Kazhdan group can be
> hyperlinear, and Pestov's sofic version of it.

> The groups below answer all three forms positively.

The groups are the `G_X` of Theorem `thm:main`, for infinite minimal subshifts `X`.  To say that some
`G_X` answers the questions, one needs an infinite minimal subshift.  This module supplies one: the
Toeplitz subshift of `GroupApproximation/Pestov91`, as a Mathlib `Subshift Bool ℤ` in the spelling
of `SimpleKazhdanSofic.Setting`.

* `toeplitzSubshift`: the orbit closure of the Toeplitz sequence, `Pestov91.subshiftCarrier`.
* `toeplitzSubshift_isMinimal`: it is minimal, from `Pestov91.eq_empty_or_univ_of_isClosed`.
* `toeplitzSubshift_infinite`: it is infinite, because the shift has no periodic points
  (`Pestov91.shiftBy_ne_self`).
* `PrintedBrownOzawaPestovAnswer` and `printedBrownOzawaPestovAnswer`: some infinite simple group with
  property (T) is sofic and hyperlinear.  This is closed, through the Palomar-ready endpoint
  `Pestov91.exists_infinite_simple_kazhdan_lef`.
* `PrintedGXAnswersBrownOzawaPestov` and `printedGXAnswersBrownOzawaPestov_of_main`: some `G_X`, with
  `X` an infinite minimal subshift, is such a group, from `thm:main` at the Toeplitz subshift.

Brown's formulation through McDuff factors is the paragraph after the finite models (section "Finite
models"), carried there.

## Manuscript status

Carries the answer sentences of the abstract and introduction; the `G_X` form is over
`PrintedSimpleKazhdanSoficMain` and closes with it.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open SymbolicDynamics.FullShift Set

/-! ## The Toeplitz subshift -/

/-- **The Toeplitz subshift** as a Mathlib subshift over the alphabet `Bool`. -/
def toeplitzSubshift : Subshift Bool ℤ where
  carrier := Pestov91.subshiftCarrier
  isClosed := Pestov91.isClosed_subshiftCarrier
  mapsTo g x hx := Pestov91.shift_mem g ⟨x, hx⟩

theorem toeplitzSubshift_carrier : toeplitzSubshift.carrier = Pestov91.subshiftCarrier :=
  rfl

/-- **The Toeplitz subshift is minimal**: a nonempty closed shift-invariant subset of it is all of
it. -/
theorem toeplitzSubshift_isMinimal : IsMinimal toeplitzSubshift := by
  intro C hC hsub hinv
  have hS : IsClosed (Subtype.val ⁻¹' C : Set Pestov91.X) := hC.preimage continuous_subtype_val
  have hinvS : ∀ y ∈ (Subtype.val ⁻¹' C : Set Pestov91.X),
      Pestov91.shiftBy 1 y ∈ (Subtype.val ⁻¹' C : Set Pestov91.X) := by
    intro y hy
    have hy' : y.1 ∈ C := hy
    exact hinv 1 hy'
  rcases Pestov91.eq_empty_or_univ_of_isClosed hS hinvS with h | h
  · left
    refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    have hmem : (⟨x, hsub hx⟩ : Pestov91.X) ∈ (Subtype.val ⁻¹' C : Set Pestov91.X) := hx
    rw [h] at hmem
    exact hmem
  · right
    refine Set.Subset.antisymm hsub fun x hx => ?_
    have hmem : (⟨x, hx⟩ : Pestov91.X) ∈ (Subtype.val ⁻¹' C : Set Pestov91.X) := by
      rw [h]
      exact Set.mem_univ _
    exact hmem

/-- **The Toeplitz subshift is infinite**: the orbit of the Toeplitz point is injective in `ℤ`. -/
theorem toeplitzSubshift_infinite : Infinite toeplitzSubshift.carrier := by
  show Infinite Pestov91.X
  have hinj : Function.Injective fun n : ℤ => Pestov91.shiftBy n Pestov91.toeplitzPoint := by
    intro i j hij
    by_contra hne
    apply Pestov91.shiftBy_ne_self Pestov91.toeplitzPoint (sub_ne_zero.mpr hne)
    apply Subtype.ext
    funext k
    have h := congrArg (fun y : Pestov91.X => y.1 (-j + k)) hij
    simp only [Pestov91.shiftBy_apply] at h
    rw [Pestov91.shiftBy_apply]
    have e1 : i - j + k = i + (-j + k) := by ring
    have e2 : j + (-j + k) = k := by ring
    rw [e1, h, e2]
  exact Infinite.of_injective _ hinj

/-! ## The answer -/

/-- **The questions of Brown and Ozawa, and Pestov's sofic version, answered positively**: there is
an infinite simple group with property (T) that is sofic and hyperlinear. -/
def PrintedBrownOzawaPestovAnswer : Prop :=
  ∃ (E : Type) (_ : Group E), Infinite E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
    IsSofic E ∧ IsHyperlinear E

/-- **The positive answer**, closed, from the infinite simple LEF Kazhdan group of
`GroupApproximation/Pestov91`. -/
theorem printedBrownOzawaPestovAnswer : PrintedBrownOzawaPestovAnswer := by
  obtain ⟨E, _, hinf, hsimple, hT, hlef⟩ := Pestov91.exists_infinite_simple_kazhdan_lef
  exact ⟨E, inferInstance, hinf, hsimple, hT, isSofic_of_isLEF hlef,
    Pestov91.isHyperlinear_of_isLEF hlef⟩

/-- **"The groups below answer all three forms positively"**: for some infinite minimal subshift
`X`, the group `G_X` is infinite, simple, Kazhdan, sofic and hyperlinear. -/
def PrintedGXAnswersBrownOzawaPestov : Prop :=
  ∃ S : Subshift Bool ℤ, Infinite S.carrier ∧ IsMinimal S ∧ Infinite (G S) ∧ IsSimpleGroup (G S) ∧
    HasKazhdanPropertyT.{0, 0} (G S) ∧ IsSofic (G S) ∧ IsHyperlinear (G S)

/-- **`thm:main` at the Toeplitz subshift answers the questions.** -/
theorem printedGXAnswersBrownOzawaPestov_of_main (h : PrintedSimpleKazhdanSoficMain) :
    PrintedGXAnswersBrownOzawaPestov := by
  obtain ⟨hinf, -, hsimple, hT, -, -, hsofic, hhyp⟩ :=
    h Bool toeplitzSubshift toeplitzSubshift_infinite toeplitzSubshift_isMinimal 3 le_rfl
  exact ⟨toeplitzSubshift, toeplitzSubshift_infinite, toeplitzSubshift_isMinimal, hinf, hsimple,
    hT, hsofic, hhyp⟩

/-- The `G_X` form of the answer gives the answer itself. -/
theorem printedBrownOzawaPestovAnswer_of_gx (h : PrintedGXAnswersBrownOzawaPestov) :
    PrintedBrownOzawaPestovAnswer := by
  obtain ⟨S, -, -, hinf, hsimple, hT, hsofic, hhyp⟩ := h
  exact ⟨G S, inferInstance, hinf, hsimple, hT, hsofic, hhyp⟩

end SimpleKazhdanSofic
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.SimpleKazhdanSofic.toeplitzSubshift_isMinimal
#audit_axioms GroupApproximation.SimpleKazhdanSofic.toeplitzSubshift_infinite
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedBrownOzawaPestovAnswer
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedGXAnswersBrownOzawaPestov_of_main
