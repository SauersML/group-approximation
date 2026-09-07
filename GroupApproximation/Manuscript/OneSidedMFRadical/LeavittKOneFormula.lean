import GroupApproximation.KOne.KappaRelations
import GroupApproximation.Leavitt.AryPurelyInfinite
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₁(L_k(1,d)) ≅ k^×/(k^×)^{d-1}`: what is proved and what is still cited

`non_mf_groups_exist.tex`, `cor:leavitt-mf-quotient`:

> `H/EL_d(R) ≅ K₁(R) ≅ k^×/(k^×)^{d-1}`

with the second isomorphism attributed to Khanh--Thanh's proof of Theorem 7.2.
After `LeavittMFQuotientKhanhThanhFree.lean` the *first* isomorphism no longer
needs that citation; this file is about the second, which is now the only part
of `cor:leavitt-mf-quotient` still resting on it.

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

## What is still open, and exactly what it is

Two clauses, stated as named propositions so that a later discharge has a
target with no slack in it:

* `ScalarSurjective k d` --- `α` is surjective, i.e. **every** class of `K₁(R)`
  is the class of a scalar.  Equivalently: every unit of `L_k(1,d)` is a
  central scalar modulo the stably elementary units.  At `d = 2` this is the
  repository's own rose-graph input `ScalarReduction`, closed there by
  `RefineLoopDischarge`; for `d ≥ 3` nothing on the tree proves it, and the
  62-module `KOne/` development that closes `d = 2` does so through
  `K₁(L_k(1,2)) = 0`, a conclusion that is **false** at `d ≥ 3`.
* `ScalarKernel k d` --- `ker α ≤ (k^×)^{d-1}`, the reverse of the exponent
  relation.  This is the clause that needs an invariant of `K₁(R)`: nothing
  proved here distinguishes two scalars, so nothing here can bound `ker α` from
  above.

`printedLeavittKOneFormula_of_inputs` assembles the printed isomorphism from
exactly those two and nothing else.

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

/-! ### The two open clauses -/

/-- **Every `K₁`-class is a scalar class.**  Equivalently, every unit of
`L_k(1,d)` is a central scalar modulo the stably elementary units.  Open for
`d ≥ 3`. -/
def ScalarSurjective : Prop := Function.Surjective (alpha k d)

/-- **A scalar killed by `κ` is a `(d-1)`-st power.**  The reverse of the
exponent relation, and the clause that needs an invariant of `K₁(R)`.  Open for
`d ≥ 3`. -/
def ScalarKernel : Prop := (alpha k d).ker ≤ unitPowSubgroup k (d - 1)

/-! ### The printed identification -/

/-- **The printed second isomorphism of `cor:leavitt-mf-quotient`.** -/
def PrintedLeavittKOneFormula : Prop :=
  Nonempty (AlgebraicKOne (AryLeavittAlgebra k d) ≃*
    (kˣ ⧸ unitPowSubgroup k (d - 1)))

/-- **The printed identification from the two open clauses and nothing else.**
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
