import GroupApproximation.Algebra.PurelyInfiniteBridge
import GroupApproximation.Leavitt.MatrixSelfSimilarity
import GroupApproximation.Leavitt.AryLeavitt
import GroupApproximation.PropertyTT.RingHypotheses

/-!
# A Leavitt family makes single-sandwich division into pure infiniteness

`non_mf_groups_exist.tex`, before `thm:mf-quotient-units`:

> The algebras `L_k(1,d)` are purely infinite simple~\cite{AbramsAranda}.

`Algebra/PurelyInfiniteBridge.lean` reduces the printed idempotent form of that
adjective to three inputs: simplicity, the sandwich clause, and one **proper
isometry**.  This module observes that a ring carrying a complete matrix family
supplies the isometry for free, and that the other two collapse into one:

* `HasSingleSandwichDivision.isSimpleRing` already derives simplicity from the
  sandwich clause, so simplicity is not a separate obligation;
* a `CompleteMatrixFamily A ι` with two distinct indices and `Nontrivial A`
  supplies the isometry, because the `left i * right i` are orthogonal
  idempotents summing to `1`, so no single one of them can be `1`.

So over any ring with a complete matrix family on at least two indices, **the
whole of "purely infinite simple" in the Ara--Goodearl--Pardo idempotent form
reduces to single-sandwich division**.

## What this isolates

For the `d`-ary Leavitt algebra that leaves exactly one open proposition,
`HasSingleSandwichDivision (AryLeavittAlgebra k d)`, and
`isPurelyInfiniteSimpleRing_aryLeavitt_of_division` states the printed adjective
conditional on it and nothing else.  That proposition is Abrams--Aranda, and it
is now the single named residue: no Ara--Goodearl--Pardo input, no simplicity
obligation, no isometry obligation.

For `d = 2` the residue is already discharged in the tree —
`BinaryLeavitt.hasSingleSandwichDivision` holds over **every** field, not only
`𝔽₂` — which is why `binaryLeavitt`-shaped consumers need nothing further.
-/

namespace GroupApproximation
namespace LeavittPurelyInfinite

open MFQuotientUnits

/-! ### A complete matrix family supplies a proper isometry -/

section Family

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal idempotents `left i * right i` of a complete matrix family are
idempotent, and orthogonal for distinct indices. -/
theorem mul_diag_diag (F : CompleteMatrixFamily A ι) (i j : ι) :
    (F.left i * F.right i) * (F.left j * F.right j)
      = if i = j then F.left i * F.right i else 0 := by
  have e₁ : (F.left i * F.right i) * (F.left j * F.right j)
      = F.left i * (F.right i * F.left j) * F.right j := by noncomm_ring
  rw [e₁, F.orthogonal]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- **A complete matrix family on two or more indices is a proper isometry.**

`right i * left i = 1` is one of the family's own equations; `left i * right i ≠ 1`
holds because a second index contributes an orthogonal idempotent that would
otherwise be forced to vanish, collapsing the ring. -/
theorem properIsometry_of_completeMatrixFamily [Nontrivial A]
    (F : CompleteMatrixFamily A ι) {i j : ι} (hij : i ≠ j) :
    F.right i * F.left i = 1 ∧ F.left i * F.right i ≠ 1 := by
  refine ⟨by simpa using F.orthogonal i i, ?_⟩
  intro hone
  -- the `j`-th diagonal idempotent is killed by the `i`-th being everything
  have hzero : F.left j * F.right j = 0 := by
    have h := mul_diag_diag F j i
    rw [if_neg (Ne.symm hij), hone, mul_one] at h
    exact h
  -- but `right j * left j = 1`, so that forces `left j = 0` and the ring is trivial
  have hj : F.right j * F.left j = 1 := by simpa using F.orthogonal j j
  have hleft : F.left j = 0 := by
    have e₁ : F.left j = (F.left j * F.right j) * F.left j := by
      rw [mul_assoc, hj, mul_one]
    rw [hzero, zero_mul] at e₁
    exact e₁
  rw [hleft, mul_zero] at hj
  exact zero_ne_one hj

/-- **Over a ring with a complete matrix family on two or more indices, pure
infiniteness in the printed idempotent form reduces to single-sandwich
division.**

Simplicity comes from the sandwich clause (`HasSingleSandwichDivision.isSimpleRing`)
and the isometry comes from the family, so nothing else is assumed. -/
theorem isPurelyInfiniteSimpleRing_of_completeMatrixFamily [Nontrivial A]
    (F : CompleteMatrixFamily A ι) {i j : ι} (hij : i ≠ j)
    (hdiv : HasSingleSandwichDivision A) :
    IsPurelyInfiniteSimpleRing A := by
  obtain ⟨hts, hst⟩ := properIsometry_of_completeMatrixFamily F hij
  exact isPurelyInfiniteSimpleRing_of_sandwich hdiv.isSimpleRing hts hst hdiv

end Family

/-! ### The `d`-ary Leavitt algebra -/

section Ary

variable (k : Type) [Field k] (d : ℕ)

/-- **The printed adjective for `L_k(1,d)`, conditional on Abrams--Aranda and
nothing else.**

Every other input the idempotent form needs is discharged: simplicity by
`HasSingleSandwichDivision.isSimpleRing`, and the proper isometry by the `d`-ary
Leavitt family through `properIsometry_of_completeMatrixFamily`.  Two distinct
indices exist because `2 ≤ d`. -/
theorem isPurelyInfiniteSimpleRing_aryLeavitt_of_division [NeZero d] (hd : 2 ≤ d)
    (hdiv : HasSingleSandwichDivision (AryLeavitt.AryLeavittAlgebra k d)) :
    IsPurelyInfiniteSimpleRing (AryLeavitt.AryLeavittAlgebra k d) := by
  have h0 : (0 : Fin d) ≠ ⟨1, hd⟩ := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  exact isPurelyInfiniteSimpleRing_of_completeMatrixFamily
    (AryLeavitt.family k d) h0 hdiv

end Ary

end LeavittPurelyInfinite
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms
  GroupApproximation.LeavittPurelyInfinite.properIsometry_of_completeMatrixFamily
#audit_axioms
  GroupApproximation.LeavittPurelyInfinite.isPurelyInfiniteSimpleRing_of_completeMatrixFamily
#audit_axioms
  GroupApproximation.LeavittPurelyInfinite.isPurelyInfiniteSimpleRing_aryLeavitt_of_division
