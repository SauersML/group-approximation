import GroupApproximation.Sofic.FaithfullyTracedCoordinateNoGo
import GroupApproximation.Sofic.HyperlinearAmplification
import GroupApproximation.Sofic.UltraproductDedekindFinite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Where `thm:kazhdan-transport` uses finite dimensionality, and why twice

Question 5 of the manuscript's questions subsection (grep the tex for
`"by other building blocks"`; probe `p:q5`, row `LI.19` of
`metadata/NON_MF_PROOF_LEDGER.md`) reads:

> Does the obstruction survive when the matrix blocks are replaced by other
> building blocks?  The proof of Theorem~\ref{thm:kazhdan-transport} uses
> finite dimensionality of `M_{d_n}(ℂ)` for the conjugation action on
> `L²(M_{d_n}(ℂ), tr_{d_n})` and for finiteness of the norm ultraproduct;
> faithful traces alone do not replace these inputs.

The open half --- for which separable `A_n` does every homomorphism into the
unitary group of `∏A_n/⊕A_n` still kill `w` --- has no formal counterpart and
can have none while it is open.  The rest of the sentence is a claim with
three parts, and this file states and proves all three.

## Naming the two uses

`finiteDimensionality_used_twice` has exactly two conjuncts, one per printed
use.

* **The conjugation action.**  `conjDouble U` is the conjugation operator
  `X ↦ U X U⋆` of `L²(M_d, tr_d)` written in row-major pair coordinates, so it
  lives in `Matrix (Y × Y) (Y × Y) ℂ`; that algebra is `B(L²(M_d, tr_d))`.
  What the printed proof consumes there is that this algebra is *finite*:
  an isometry of the conjugation space is unitary, and more generally a
  one-sided inverse is two-sided.  For a finite coordinate type that is
  `IsDedekindFiniteMonoid (Matrix (Y × Y) (Y × Y) ℂ)`, which the pinned
  Mathlib supplies from `IsStablyFiniteRing ℂ`.
* **Finiteness of the norm ultraproduct.**  This is `kt_06_ultraproduct_finite`
  (step KT.06), proved by the printed polar correction at each finite
  coordinate.

The two are genuinely two: the first is about the operator algebra of a single
coordinate's Hilbert space, the second about the quotient algebra of the whole
sequence, and neither statement mentions the other's object.

## Why neither use is removable

The manuscript justifies the necessity of the *first* use in its limitations
paragraph, in one line: for a finite factor `M` in standard form the two
commuting actions generate `Z(M)' = B(L²(M, τ))`, and *in infinite dimension
this is not a finite C⋆-algebra*.  `not_dedekindFinite_infiniteDimensionalModel`
is that line, in the sharpest and cheapest form available: on an
infinite-dimensional coordinate space the two shifts satisfy `T S = 1` and
`S T ≠ 1`, so the operator algebra of the conjugation space is not
Dedekind-finite --- not merely "not a finite C⋆-algebra".

Two honest notes about that witness.

*It is algebraic, and deliberately so.*  The failure needs no norm: `T S = 1`
with `S T ≠ 1` is an identity in `Module.End ℂ (ℕ → ℂ)`.  Boundedness would
only be needed to *represent* the failure inside a C⋆-algebra of operators,
and the pinned Mathlib has no `ℓ²(ℕ)` shift to represent it with.  What the
finite-dimensional side consumes is Dedekind finiteness and nothing more
(`isDedekindFinite_finiteDimensionalModel` is the contrast, for an arbitrary
finite-dimensional space), so the algebraic form is the exact hypothesis at
issue.

*It is not a restatement of the second use.*  The corona statement
`kt_06_ultraproduct_finite` is about `ℓ∞(M_{d_n})/c₀(M_{d_n})`, and its proof
runs through coordinatewise polar correction; the shift witness is about a
single infinite-dimensional coordinate.

The necessity of the *pair* --- that faithful traces do not replace them --- is
`FaithfullyTracedCoordinates.manuscriptFaithfullyTracedCoordinateNoGo`, which
refutes the whole transport statement over stably finite coordinates carrying
faithful tracial states, with every other hypothesis copied verbatim.  That is
the third conjunct of `kazhdanTransport_finiteDimensionalInputs`, and it is
where the printed clause *faithful traces alone do not replace these inputs*
is discharged.

What no declaration here says, because no declaration can, is that the printed
proof uses finite dimensionality at *only* these two points.  That is a claim
about a text.  What is proved is that both are used, both hold for matrix
coordinates, and neither survives the passage to infinite-dimensional or
merely faithfully traced coordinates.
-/

namespace GroupApproximation
namespace KazhdanTransportFiniteDimensionalInputs

open Matrix

universe w

noncomputable section

/-! ## Point one: the conjugation model of a finite coordinate algebra -/

/-- **The conjugation model is finite: an isometry of `L²(M_d, tr_d)` is
unitary.**  `conjDouble U` lives in this algebra, and this is the property the
printed conjugation-action step consumes. -/
theorem conjugationModel_isometry_unitary (Y : FiniteModel)
    {a : Matrix (Y × Y) (Y × Y) ℂ} (ha : star a * a = 1) : a * star a = 1 :=
  mul_eq_one_symm ha

/-- The same in the one-sided-inverse form, which is what the corona
statements are phrased with. -/
theorem conjugationModel_mul_eq_one_symm (Y : FiniteModel)
    {a b : Matrix (Y × Y) (Y × Y) ℂ} (hab : a * b = 1) : b * a = 1 :=
  mul_eq_one_symm hab

/-- The conjugation operator of a unitary is an isometry of the conjugation
model, so the previous theorem applies to it: this records that the algebra in
which the printed conjugation action lives is the one just shown finite. -/
theorem conjDouble_isometry_unitary (Y : FiniteModel) {U : Matrix Y Y ℂ}
    (h : star (conjDouble U) * conjDouble U = 1) :
    conjDouble U * star (conjDouble U) = 1 :=
  conjugationModel_isometry_unitary Y h

/-! ## Dropping finite dimensionality: the shifts -/

/-- The forward shift of an infinite coordinate sequence. -/
def shiftUpFun (v : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | (n + 1) => v n

/-- The forward shift as an operator on the infinite-dimensional coordinate
space.  It is a one-sided inverse of the backward shift and nothing more:
that is the whole of the failure. -/
def shiftUp : Module.End ℂ (ℕ → ℂ) where
  toFun := shiftUpFun
  map_add' u v := by
    funext n
    cases n <;> simp [shiftUpFun]
  map_smul' c v := by
    funext n
    cases n <;> simp [shiftUpFun]

/-- The backward shift. -/
def shiftDown : Module.End ℂ (ℕ → ℂ) where
  toFun v := fun n ↦ v (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem shiftDown_mul_shiftUp : shiftDown * shiftUp = 1 := by
  refine LinearMap.ext fun v ↦ ?_
  funext n
  rfl

theorem shiftUp_mul_shiftDown_ne_one : shiftUp * shiftDown ≠ 1 := by
  intro h
  have hv : ((shiftUp * shiftDown) (fun n ↦ if n = 0 then (1 : ℂ) else 0)) 0
      = ((1 : Module.End ℂ (ℕ → ℂ)) (fun n ↦ if n = 0 then (1 : ℂ) else 0)) 0 := by
    rw [h]
  have hleft :
      ((shiftUp * shiftDown) (fun n ↦ if n = 0 then (1 : ℂ) else 0)) 0
        = 0 := rfl
  have hright :
      ((1 : Module.End ℂ (ℕ → ℂ)) (fun n ↦ if n = 0 then (1 : ℂ) else 0)) 0
        = 1 := by
    simp
  rw [hleft, hright] at hv
  exact zero_ne_one hv

/-- **In infinite dimension the operator algebra of the conjugation space is
not finite.**  This is the manuscript's own justification for the first use,
in the form in which the C⋆-norm plays no part: the shifts already break
Dedekind finiteness. -/
theorem not_dedekindFinite_infiniteDimensionalModel :
    ∃ S T : Module.End ℂ (ℕ → ℂ), T * S = 1 ∧ S * T ≠ 1 :=
  ⟨shiftUp, shiftDown, shiftDown_mul_shiftUp, shiftUp_mul_shiftDown_ne_one⟩

/-- The contrast, at an arbitrary finite-dimensional space: there, and only
there, is a one-sided inverse two-sided.  Finite dimensionality is exactly the
hypothesis at issue. -/
theorem isDedekindFinite_finiteDimensionalModel {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {f g : Module.End ℂ V}
    (h : f * g = 1) : g * f = 1 :=
  mul_eq_one_symm h

/-! ## The printed sentence -/

/-- **Finite dimensionality of `M_{d_n}(ℂ)` is used twice, and both uses hold
for matrix coordinates.**  Exactly two conjuncts, one per printed use: the
conjugation action on `L²(M_{d_n}, tr_{d_n})`, and finiteness of the norm
ultraproduct. -/
theorem finiteDimensionality_used_twice :
    (∀ (Y : FiniteModel) (a : Matrix (Y × Y) (Y × Y) ℂ),
        star a * a = 1 → a * star a = 1) ∧
      (∀ (Z : ℕ → FiniteModel) [∀ n, Nonempty (Z n)]
          (sigma : NormMatrixCStarCorona (fun n ↦ Z n)),
          star sigma * sigma = 1 → sigma * star sigma = 1) := by
  constructor
  · intro Y a ha
    exact mul_eq_one_symm ha
  · intro Z _ sigma h
    exact kt_06_ultraproduct_finite Z h

/-- **Question 5's supporting assertions, as one statement.**

1. The conjugation action's input: the operator algebra of `L²(M_d, tr_d)` is
   finite.
2. The norm ultraproduct's input: `B_ω` is finite.
3. Neither input survives the loss of finite dimensionality: on an
   infinite-dimensional coordinate space the operator algebra is not even
   Dedekind-finite.
4. And faithful traces do not replace them: the transport statement with
   stably finite, faithfully traced coordinates and every other hypothesis
   unchanged is false.

Conjuncts 1 and 2 are the two printed uses; conjuncts 3 and 4 are the printed
clause *faithful traces alone do not replace these inputs*, split into the
reason the manuscript gives for it and the manuscript's own counterexample. -/
theorem kazhdanTransport_finiteDimensionalInputs :
    (∀ (Y : FiniteModel) (a : Matrix (Y × Y) (Y × Y) ℂ),
        star a * a = 1 → a * star a = 1) ∧
      (∀ (Z : ℕ → FiniteModel) [∀ n, Nonempty (Z n)]
          (sigma : NormMatrixCStarCorona (fun n ↦ Z n)),
          star sigma * sigma = 1 → sigma * star sigma = 1) ∧
      (∃ S T : Module.End ℂ (ℕ → ℂ), T * S = 1 ∧ S * T ≠ 1) ∧
      ¬ FaithfullyTracedCoordinates.FaithfullyTracedCoordinateTransport.{w} :=
  ⟨finiteDimensionality_used_twice.1, finiteDimensionality_used_twice.2,
    not_dedekindFinite_infiniteDimensionalModel,
    FaithfullyTracedCoordinates.manuscriptFaithfullyTracedCoordinateNoGo⟩

end

end KazhdanTransportFiniteDimensionalInputs
end GroupApproximation
