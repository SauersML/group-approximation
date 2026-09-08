import GroupApproximation.Leavitt.AryDivision
import GroupApproximation.Leavitt.LeavittPurelyInfinite

/-!
# `L_k(1,d)` is purely infinite simple, for every field and every `d ≥ 2`

`non_mf_groups_exist.tex`, before `thm:mf-quotient-units`:

> The algebras `L_k(1,d)` are purely infinite simple~\cite{AbramsAranda}.

This closes that printed adjective in the Ara--Goodearl--Pardo **idempotent**
form — the one `thm:mf-quotient-units` and `AGPMatrixReduction` consume — for an
arbitrary field and every `d ≥ 2`, with nothing assumed.

## What it took, and what it did not

The chain is four stages of generalising the binary development from arity `2` to
arity `d`:

| stage | module |
|---|---|
| words layer | `AryWords.lean` |
| monomial normal form | `AryNormalForm.lean` |
| cylinder partition, annihilating word | `AryKillWord.lean` |
| monomial representation, single-sandwich division | `AryDivision.lean` |

and then two facts that were already in the tree and needed no arity at all:
`HasSingleSandwichDivision.isSimpleRing` derives simplicity from the sandwich
clause, and `LeavittPurelyInfinite.properIsometry_of_completeMatrixFamily`
supplies the proper isometry from the `d`-ary family itself.  So of the three
inputs the idempotent form needs — simplicity, the sandwich clause, an isometry —
only the sandwich clause ever had to be generalised.

**No Ara--Goodearl--Pardo input appears anywhere in this chain.**  In particular
neither their §1 comparison theory nor Proposition 1.5 is used: the route runs
`AryDivision` → `PurelyInfiniteBridge`, and the bridge only needs one proper
isometry and the sandwich clause.

## Where `2 ≤ d` is load-bearing

In exactly two places, and they are the same fact: the annihilating word
`i₀^m i₁` needs two distinct letters, and
`properIsometry_of_completeMatrixFamily` needs two distinct indices.  At `d = 1`,
`L_k(1,1) ≅ k[x, x⁻¹]` is a commutative principal ideal domain — neither simple
nor purely infinite — so the hypothesis is not merely unavailable but false, and
the statement below would be vacuous rather than wrong.
-/

namespace GroupApproximation
namespace AryLeavitt

variable (k : Type) [Field k] (d : ℕ)

/-- **Single-sandwich division for `L_k(1,d)`**, in the tree's own predicate. -/
theorem hasSingleSandwichDivision (hd : 2 ≤ d) :
    HasSingleSandwichDivision (AryLeavittAlgebra k d) :=
  fun _ ha => exists_mul_mul_eq_one k d hd ha

/-- **The printed adjective for `L_k(1,d)`, unconditionally.**

`Abrams--Aranda`'s theorem, in the Ara--Goodearl--Pardo idempotent form, for
every field `k` and every `d ≥ 2`. -/
theorem isPurelyInfiniteSimpleRing (hd : 2 ≤ d) :
    MFQuotientUnits.IsPurelyInfiniteSimpleRing (AryLeavittAlgebra k d) := by
  haveI : NeZero d := ⟨by omega⟩
  exact LeavittPurelyInfinite.isPurelyInfiniteSimpleRing_aryLeavitt_of_division
    k d hd (hasSingleSandwichDivision k d hd)

end AryLeavitt
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AryLeavitt.hasSingleSandwichDivision
#audit_axioms GroupApproximation.AryLeavitt.isPurelyInfiniteSimpleRing
