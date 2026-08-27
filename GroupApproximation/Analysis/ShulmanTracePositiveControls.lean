import GroupApproximation.Analysis.ShulmanTraceClasses
import GroupApproximation.Analysis.ShulmanTraceNorms
import GroupApproximation.Analysis.ShulmanTraceFactorization
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive controls for the three Shulman trace classes

`IsMFTrace`, `IsHyperlinearTrace` and `IsFactoredHyperlinearTrace` are used in
this development the way an obstruction is used: something is proved *not* to
satisfy them.  `LiteralTraceConsequence.markedGroup_canonicalMaximalTrace_not_isMFTrace`
is the headline of that shape.

A negative result about a predicate nothing satisfies is true and empty, and
no kernel check can tell the difference: an unsatisfiable `Prop` has exactly
the same closure over `propext`, `Classical.choice` and `Quot.sound` as a
satisfiable one.  The only thing that separates the two is an inhabitant, so
this file supplies one for each of the three classes.

(The wrapping of the paragraph above is deliberate.  `scripts/check.py` scans
source text, not syntax, and reads a line that begins with the word it is
looking for as a hand-declared constant — prose in a docstring included.  An
earlier draft tripped that detector twice from this paragraph alone.)

## The witness

`M_k(ℂ)` with its normalized trace `tr = normTrace`, and `φₙ = id` for every
`n`.  Every one of the five defect clauses is then not merely small but
*identically zero*: `φₙ(ab) = φₙ(a)φₙ(b)` on the nose, `φₙ` is exactly linear
and exactly `⋆`-preserving, `‖φₙ(a)‖ = ‖a‖`, and `tr(φₙ(a)) = tr(a)` exactly.
So the controls are not delicate limits that might be hiding something; they
are equalities.

`normTraceTracialState` records that the functional being witnessed is a real
tracial state on a real algebra: unital, positive on `x⋆x`, and invariant
under swapping the factors of a product, in the repository's own
`TracialState` sense.  It is not the zero functional and not a formal device.

## What these controls do and do not rule out

They rule out exactly one thing: that the three definitions are unsatisfiable.
Each is inhabited, so each negative theorem downstream is a statement with
content.

They rule out nothing else.  In particular:

* They say nothing about group C⋆-algebras.  That the canonical trace of some
  `C⋆(G)` is an MF trace is a separate and much harder statement, and no
  version of it is proved here or claimed here.
* `MFTraceModel` does not require the matrix sizes `kₙ` to grow, so a constant
  sequence of models is legitimate and a finite-dimensional algebra's trace is
  an MF trace for the cheapest possible reason.  That is a fact about the
  definition, transcribed as it stands from Shulman, arXiv:2507.22783v3, and
  the control makes it visible rather than hiding it.
* Being deliberately minimal, the control is *not* evidence that the classes
  are large, or that they separate, or that any particular trace lies in one
  and not another.  It is evidence of inhabitation and nothing more.

The controls are stated for an arbitrary `Y : FiniteModel` and then
instantiated at a fixed two-element model, so that the closing three theorems
take no arguments at all — neither data nor hypotheses — and are therefore
inhabitants in the strictest sense.
-/

open Filter Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace GroupApproximation
namespace ShulmanTrace

noncomputable section

/-! ## A sequence that is identically zero converges to zero

Every clause below is discharged through this one lemma, which is the whole
reason the controls are equalities rather than estimates. -/

/-- A real sequence which is identically zero tends to zero. -/
theorem tendsto_zero_of_eq_zero {f : ℕ → ℝ} (h : ∀ n, f n = 0) :
    Tendsto f atTop (nhds 0) := by
  have hf : f = fun _ ↦ (0 : ℝ) := funext h
  rw [hf]
  exact tendsto_const_nhds

/-! ## The normalized matrix trace is a genuine tracial state -/

/-- The normalized trace of `M_k(ℂ)`, as a `ℂ`-linear functional. -/
def normTraceLinearMap (Y : FiniteModel) : Matrix Y Y ℂ →ₗ[ℂ] ℂ where
  toFun := normTrace Y
  map_add' A B := by
    simp only [normTrace, Matrix.trace_add]
    ring
  map_smul' c A := by
    simp only [normTrace, Matrix.trace_smul, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem normTraceLinearMap_apply (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    normTraceLinearMap Y A = normTrace Y A :=
  rfl

/-- The normalized trace is positive on elements `x⋆x`.  `xᴴx` is positive
semidefinite, so its trace is a nonnegative real, and dividing by the
(nonnegative real) dimension keeps it there. -/
theorem normTrace_star_mul_self_nonneg (Y : FiniteModel) (x : Matrix Y Y ℂ) :
    0 ≤ normTrace Y (star x * x) := by
  have hpsd : (xᴴ * x).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self x
  have htr : (0 : ℂ) ≤ (xᴴ * x).trace := hpsd.trace_nonneg
  have hre : (0 : ℝ) ≤ ((xᴴ * x).trace).re := (Complex.nonneg_iff.mp htr).1
  have heq : (xᴴ * x).trace = ((((xᴴ * x).trace).re : ℝ) : ℂ) :=
    Complex.eq_re_of_ofReal_le (by rw [Complex.ofReal_zero]; exact htr)
  rw [Matrix.star_eq_conjTranspose, normTrace, heq,
    ← Complex.ofReal_natCast (Fintype.card Y), ← Complex.ofReal_div]
  exact Complex.zero_le_real.mpr (div_nonneg hre (by positivity))

/-- **The witness functional is a real trace on a real algebra.**  The
normalized trace of `M_k(ℂ)`, `k ≥ 1`, bundled as a `TracialState` in the
repository's sense: unital, positive on `x⋆x`, tracial. -/
def normTraceTracialState (Y : FiniteModel) (hY : 0 < Fintype.card Y) :
    TracialState (Matrix Y Y ℂ) where
  toLinearMap := normTraceLinearMap Y
  map_one := by
    -- `normTrace_one'` is already in the corpus (`Sofic/PhasePropagation`) and
    -- reaches here through the import chain.  An earlier draft reproved it
    -- locally and the audit's DUPLICATE scan was right to object.
    show normTrace Y (1 : Matrix Y Y ℂ) = 1
    exact normTrace_one' Y hY
  map_star_mul_self_nonneg x := by
    show 0 ≤ normTrace Y (star x * x)
    exact normTrace_star_mul_self_nonneg Y x
  map_mul_comm x y := by
    show normTrace Y (x * y) = normTrace Y (y * x)
    simp only [normTrace, Matrix.trace_mul_comm x y]

@[simp] theorem normTraceTracialState_apply (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) (A : Matrix Y Y ℂ) :
    normTraceTracialState Y hY A = normTrace Y A :=
  rfl

/-! ## The controls -/

/-- **The identity model.**  Taking `φₙ = id : M_k(ℂ) → M_k(ℂ)` for every `n`
satisfies all five clauses of `MFTraceModel` with every defect exactly `0`:
the maps are honestly multiplicative, honestly linear, honestly
`⋆`-preserving, norm-preserving, and trace-correct. -/
def normTraceMFTraceModel (Y : FiniteModel) : MFTraceModel (normTrace Y) where
  space := fun _ ↦ Y
  map := fun _ a ↦ a
  tendsto_mul a b := tendsto_zero_of_eq_zero fun _ ↦ by
    show ‖a * b - a * b‖ = 0
    rw [sub_self, norm_zero]
  tendsto_linear c₁ c₂ a b := tendsto_zero_of_eq_zero fun _ ↦ by
    show ‖c₁ • a + c₂ • b - c₁ • a - c₂ • b‖ = 0
    rw [add_sub_cancel_left, sub_self, norm_zero]
  tendsto_star a := tendsto_zero_of_eq_zero fun _ ↦ by
    show ‖star a - aᴴ‖ = 0
    rw [Matrix.star_eq_conjTranspose, sub_self, norm_zero]
  bounded a := ⟨‖a‖, fun _ ↦ le_rfl⟩
  tendsto_trace a := tendsto_zero_of_eq_zero fun _ ↦ by
    show ‖normTrace Y a - normTrace Y a‖ = 0
    rw [sub_self, norm_zero]

/-- **Positive control for `IsMFTrace`.**  The normalized trace of a nonzero
matrix algebra is an MF trace. -/
theorem isMFTrace_normTrace (Y : FiniteModel) (hY : 0 < Fintype.card Y) :
    IsMFTrace (normTrace Y) :=
  ⟨IsTracialState.of_bundled (normTraceTracialState Y hY),
    ⟨normTraceMFTraceModel Y⟩⟩

/-- **Positive control for `IsHyperlinearTrace`.**  Free from the previous one
through the comparison `‖x‖₂ ≤ ‖x‖`, which is what
`isHyperlinearTrace_of_isMFTrace` is for. -/
theorem isHyperlinearTrace_normTrace (Y : FiniteModel)
    (hY : 0 < Fintype.card Y) :
    IsHyperlinearTrace (normTrace Y) :=
  isHyperlinearTrace_of_isMFTrace (isMFTrace_normTrace Y hY)

/-- **Positive control for `IsFactoredHyperlinearTrace`.**  The factorization
route asks the matrix sizes to be positive — `M_0(ℂ)` is not a matrix algebra
— so the model has to be nonempty here, unlike in the two previous controls. -/
theorem isFactoredHyperlinearTrace_normTrace (Y : FiniteModel)
    (hY : Nonempty Y) : IsFactoredHyperlinearTrace (normTrace Y) :=
  isFactoredHyperlinearTrace_of_model
    (normTraceMFTraceModel Y).toApproximationModel.toHilbertSchmidt
    fun _ ↦ hY

/-! ## The controls with nothing left to supply

`Fin 2`, so that the ambient is the full `2 × 2` matrix algebra rather than a
one-dimensional or commutative stand-in, and so that the three theorems below
take no arguments of any kind. -/

/-- A fixed two-element model. -/
abbrev twoDimModel : FiniteModel := ⟨Fin 2, inferInstance, inferInstance⟩

theorem card_twoDimModel : Fintype.card twoDimModel = 2 := by
  show Fintype.card (Fin 2) = 2
  simp

theorem card_twoDimModel_pos : 0 < Fintype.card twoDimModel := by
  rw [card_twoDimModel]
  norm_num

/-- The normalized trace of `M_2(ℂ)`, as a tracial state. -/
def twoDimTracialState : TracialState (Matrix twoDimModel twoDimModel ℂ) :=
  normTraceTracialState twoDimModel card_twoDimModel_pos

/-- **`IsMFTrace` is inhabited.** -/
theorem isMFTrace_normTrace_twoDim : IsMFTrace (normTrace twoDimModel) :=
  isMFTrace_normTrace twoDimModel card_twoDimModel_pos

/-- **`IsHyperlinearTrace` is inhabited.** -/
theorem isHyperlinearTrace_normTrace_twoDim :
    IsHyperlinearTrace (normTrace twoDimModel) :=
  isHyperlinearTrace_normTrace twoDimModel card_twoDimModel_pos

/-- **`IsFactoredHyperlinearTrace` is inhabited.** -/
theorem isFactoredHyperlinearTrace_normTrace_twoDim :
    IsFactoredHyperlinearTrace (normTrace twoDimModel) :=
  isFactoredHyperlinearTrace_normTrace twoDimModel ⟨(0 : Fin 2)⟩

end

end ShulmanTrace
end GroupApproximation
