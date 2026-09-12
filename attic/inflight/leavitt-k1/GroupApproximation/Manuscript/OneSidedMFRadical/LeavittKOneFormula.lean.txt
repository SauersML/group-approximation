import GroupApproximation.KOne.KappaRelations
import GroupApproximation.Leavitt.AryPurelyInfinite
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`: the two clauses and their assembly

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient`:

> `H/EL_d(R) ≅ K₁(R) ≅ k^×/(k^×)^{d-1}`

with the second isomorphism attributed to Khanh--Thanh's proof of Theorem 7.2.
After `LeavittMFQuotientKhanhThanhFree.lean` the *first* isomorphism no longer
needs that citation.  This file is about the second, which no longer needs it
either: both of its clauses below are theorems, and
`LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula` is the printed
isomorphism at every field and every `d ≥ 2`.

## What is proved here, unconditionally

* `kappa_surjective_aryLeavitt` --- `κ : Rˣ → K₁(R)` is **surjective** for
  `R = L_k(1,d)`, `d ≥ 2`.  This is the surjectivity clause of
  Ara--Goodearl--Pardo Theorem 2.4 for the Leavitt algebras, and it comes from
  rank-`n` Gaussian elimination, not from either citation.
* `alpha_pow_eq_one` --- the composite `α : k^× → Rˣ → K₁(R)` kills
  `(k^×)^{d-1}`, so it factors through `k^×/(k^×)^{d-1}`.  This is the exponent
  relation, and it is the half of the printed identification that follows from
  the `d`-ary Leavitt family alone: a central unit decomposes into `d` corner
  insertions, each of which is `κ`-equal to the unit itself.

## The two clauses

Two clauses, stated as named propositions so that a discharge has a target
with no slack in it.  Both are proved at every field and every `d ≥ 2`, in
modules that import this one:

* `ScalarSurjective k d` --- `α` is surjective, i.e. **every** class of `K₁(R)`
  is the class of a scalar.  Equivalently: every unit of `L_k(1,d)` is a
  central scalar modulo the stably elementary units.  At `d = 2` this is the
  repository's own rose-graph input `ScalarReduction`, closed there by
  `RefineLoopDischarge` through `K₁(L_k(1,2)) = 0`, a conclusion that is
  **false** at `d ≥ 3`.  At every `d ≥ 2` it is
  `KhanhThanhDiagonal.scalarSurjective_holds`
  (`Manuscript/OneSidedMFRadical/KhanhThanhDecompositionClosed.lean`), from the
  arity-`d` elimination `AryLeavitt.narrowReduction_holds`.
* `ScalarKernel k d` --- `ker α ≤ (k^×)^{d-1}`, the reverse of the exponent
  relation.  This is the clause that needs an invariant of `K₁(R)`, since
  nothing proved here distinguishes two scalars.  The invariant is the
  regularized determinant on the Toeplitz space of words, and the clause is
  `scalarKernel` (`KOne/LeavittKOneScalarKernel.lean`).

`printedLeavittKOneFormula_of_inputs` assembles the printed isomorphism from
exactly those two and nothing else.

`scalarSurjective_of_scalarReduction` further reduces the *first* of them to
the repository's own vocabulary: it follows from
`MatrixDiagonalization.ScalarReduction (L_k(1,d))` --- the `d`-ary rose-graph
input --- together with `CentralUnitsAreScalars`, i.e. `Z(L_k(1,d)) = k`.  This
is the route `scalarSurjective_holds` takes.  `ScalarKernel` has no such
reduction here.

## Calibration

At `d = 2` both propositions hold but carry no information: `K₁ = 0`, so
`ScalarSurjective` is the statement that the trivial group is covered and
`ScalarKernel` reads `c = e^1`, true with `e = c`.  Nothing should be validated
against `d = 2`.  The first genuinely non-vacuous case is `d = 3` over a field
with a non-square unit, for instance `k = 𝔽₅`, where the printed answer is
`ℤ/2`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace LeavittKOneFormula

open AryLeavitt AlgebraicK

variable (k : Type) [Field k] (d : ℕ)

/-! ### The scalar map into `K₁` -/

/-- The units of `k`, as units of `L_k(1,d)`. -/
def scalarUnits : kˣ →* (AryLeavittAlgebra k d)ˣ :=
  Units.map (algebraMap k (AryLeavittAlgebra k d)).toMonoidHom

/-- **`α : k^× → K₁(L_k(1,d))`**, the map the printed identification is about. -/
noncomputable def alpha : kˣ →* AlgebraicKOne (AryLeavittAlgebra k d) :=
  (kappa (AryLeavittAlgebra k d)).comp (scalarUnits k d)

theorem alpha_apply (c : kˣ) :
    alpha k d c = kappa (AryLeavittAlgebra k d) (scalarUnits k d c) := rfl

/-- The subgroup of `(d-1)`-st powers of `k^×`. -/
def unitPowSubgroup (m : ℕ) : Subgroup kˣ :=
  (powMonoidHom m : kˣ →* kˣ).range

/-! ### The two unconditional facts -/

/-- **`κ` is surjective for the `d`-ary Leavitt algebra.**  Ara--Goodearl--Pardo
Theorem 2.4's surjectivity clause, from Gaussian elimination alone. -/
theorem kappa_surjective_aryLeavitt (hd : 2 ≤ d) :
    Function.Surjective (kappa (AryLeavittAlgebra k d)) := by
  haveI : NeZero d := ⟨by omega⟩
  exact AlgebraicK.kappa_surjective (AryLeavitt.hasSingleSandwichDivision k d hd)

/-- **The exponent relation.**  `α(c)^{d-1} = 1` for every scalar `c`: the
`d`-ary family decomposes `c` into `d` corner insertions, each `κ`-equal to
`c`. -/
theorem alpha_pow_eq_one (hd : 2 ≤ d) (c : kˣ) :
    alpha k d c ^ (d - 1) = 1 := by
  haveI : NeZero d := ⟨by omega⟩
  have hcentral : ∀ x : AryLeavittAlgebra k d,
      ((scalarUnits k d c : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) * x =
        x * ((scalarUnits k d c : (AryLeavittAlgebra k d)ˣ) :
          AryLeavittAlgebra k d) := by
    intro x
    exact (Algebra.commutes (c : k) x)
  have h := AlgebraicK.kappa_central_pow_card_sub_one
    (AryLeavitt.hasSingleSandwichDivision k d hd) (AryLeavitt.family k d)
    (scalarUnits k d c) hcentral
  rwa [Fintype.card_fin] at h

/-- The `(d-1)`-st powers lie in the kernel of `α`. -/
theorem unitPowSubgroup_le_ker (hd : 2 ≤ d) :
    unitPowSubgroup k (d - 1) ≤ (alpha k d).ker := by
  rintro _ ⟨e, rfl⟩
  rw [MonoidHom.mem_ker]
  show alpha k d (e ^ (d - 1)) = 1
  rw [map_pow]
  exact alpha_pow_eq_one k d hd e

/-! ### The two clauses -/

/-- **Every `K₁`-class is a scalar class.**  Equivalently, every unit of
`L_k(1,d)` is a central scalar modulo the stably elementary units.  Proved at
every field and every `d ≥ 2`: `KhanhThanhDiagonal.scalarSurjective_holds`. -/
def ScalarSurjective : Prop := Function.Surjective (alpha k d)

/-- **A scalar killed by `κ` is a `(d-1)`-st power.**  The reverse of the
exponent relation, and the clause that needs an invariant of `K₁(R)`.  Proved at
every field and every `d ≥ 2`: `LeavittKOneFormula.scalarKernel`. -/
def ScalarKernel : Prop := (alpha k d).ker ≤ unitPowSubgroup k (d - 1)

/-- **Every central unit of `L_k(1,d)` is a scalar.**  True for `d ≥ 2`,
because the centre of `L_k(1,d)` is `k`.

**This is now a theorem**: `KOne/AryCentralUnitsAreScalars.centralUnitsAreScalars`
discharges it at every field and every `d ≥ 2`, from
`Leavitt/LeavittCenter.eq_smul_one_of_central` (a central element is `a • 1`)
together with the fact that `0` is not invertible.

The paragraph that stood here said the opposite, and both of its claims have
since become false.  It said the proposition was out of reach at every arity
because it needed the reduced monomial basis, which the tree carried only as a
cited input and for which no `LinearIndependent` result existed.  Neither is
true now: the statement never needed the basis, only the centre computation;
and `Leavitt/AryLeavittBasis.lean` does prove independence for the degree-zero
monomials, which is the layer every `K₁` argument here uses.  The correction is
recorded rather than deleted, because the false claim was load-bearing — it is
why `scalarSurjective_of_scalarReduction` below was described as a dead
reduction, and it is not. -/
def CentralUnitsAreScalars : Prop :=
  ∀ c : (AryLeavittAlgebra k d)ˣ,
    (∀ x : AryLeavittAlgebra k d,
        ((c : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d) * x =
          x * ((c : (AryLeavittAlgebra k d)ˣ) : AryLeavittAlgebra k d)) →
      ∃ a : kˣ, c = scalarUnits k d a

/-- **`ScalarSurjective` from the repository's own rose-graph input.**

`MatrixDiagonalization.ScalarReduction R` --- every unit is a central unit
times a stably elementary one --- is the proposition the `KOne/` development
closes at `d = 2` through `RefineLoopDischarge`.  Together with the
identification of the centre it gives the first clause, so that clause
does not have to be attacked directly: it is the `d`-ary rose-graph input plus
`Z(L_k(1,d)) = k`.

The two hypotheses do real work in opposite directions and neither is implied
by the other: `ScalarReduction` says the quotient is generated by *central*
units, `CentralUnitsAreScalars` says those are *scalars*. -/
theorem scalarSurjective_of_scalarReduction (hd : 2 ≤ d)
    (hsr : MatrixDiagonalization.ScalarReduction (AryLeavittAlgebra k d))
    (hcen : CentralUnitsAreScalars k d) :
    ScalarSurjective k d := by
  intro z
  obtain ⟨u, hu⟩ := kappa_surjective_aryLeavitt k d hd z
  obtain ⟨c, hccen, hcu⟩ := hsr u
  obtain ⟨a, rfl⟩ := hcen c hccen
  refine ⟨a, ?_⟩
  have h1 := AlgebraicK.kappa_eq_one_of_mem_stableUnits hcu
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [alpha_apply, h1, hu]

/-! ### The printed identification -/

/-- **The printed second isomorphism of `cor:leavitt-mf-quotient`.** -/
def PrintedLeavittKOneFormula : Prop :=
  Nonempty (AlgebraicKOne (AryLeavittAlgebra k d) ≃*
    (kˣ ⧸ unitPowSubgroup k (d - 1)))

/-- **The printed identification from the two clauses and nothing else.**
The exponent relation is supplied here, not assumed. -/
theorem printedLeavittKOneFormula_of_inputs (hd : 2 ≤ d)
    (hsurj : ScalarSurjective k d) (hker : ScalarKernel k d) :
    PrintedLeavittKOneFormula k d := by
  have hkereq : (alpha k d).ker = unitPowSubgroup k (d - 1) :=
    le_antisymm hker (unitPowSubgroup_le_ker k d hd)
  refine ⟨((QuotientGroup.quotientKerEquivOfSurjective (alpha k d) hsurj).symm).trans
    (QuotientGroup.quotientMulEquivOfEq hkereq)⟩

end LeavittKOneFormula
end OneSidedMFRadical
end Manuscript
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula.kappa_surjective_aryLeavitt
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula.alpha_pow_eq_one
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula.printedLeavittKOneFormula_of_inputs
#audit_axioms
  GroupApproximation.Manuscript.OneSidedMFRadical.LeavittKOneFormula.scalarSurjective_of_scalarReduction
