import GroupApproximation.CharClass.SliceSplitV
import GroupApproximation.CharClass.SliceTrivialEuler

/-!
# The roots of `V`, named

`splitRelation_V` takes its roots as a parameter agreeing with the Euler classes
of the lines on the range.  This file names that family and discharges the half
of the agreement that is settled.

The three constant summands contribute a root of zero, which is
`lineEulerOf_const`.  The line in block `(j, i)` contributes the pulled-back
generator of the `j`-th projective factor, and that identification is the one
piece of geometry left; it is stated here as what a consumer must supply, against
these names, so that nobody has to guess the spelling of the projection or of the
positivity proof.

Note the multiplicity: the block index runs over pairs, and every `i` in block
`j` gives the **same** generator, so the family is far from injective and the
symmetric functions of it are genuinely repeated.

## Main declarations

* `baseYFactor` — the projection onto the `j`-th projective factor.
* `vRoot` — **the root family.**
* `lineEulerOf_vLineY_inl` — the constant summands contribute zero.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn
open GroupApproximation.CharClass.LH

noncomputable section

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- The projection of the base onto its `j`-th projective factor. -/
def baseYFactor (dd : Fin ℓ → ℕ) (j : Fin ℓ) : C(baseY dd, CP (dd j)) :=
  ⟨fun y => y j, continuous_apply j⟩

/-- **The root family.**  Zero on the three constant lines; on a line of block
`(j, i)` the generator of the `j`-th projective factor, pulled back.  Every `i` in
a block gives the same generator, which is where the multiplicity `dd j` comes
from. -/
def vRoot (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) (l : ℕ) :
    Hmod2 (TopCat.of (baseY dd)) 2 :=
  match (vIndexEquiv dd).symm ⟨l % lixRank dd, Nat.mod_lt _ (lixRank_pos dd)⟩ with
  | Sum.inl _ => 0
  | Sum.inr b => pull (cmap (baseYFactor dd b.1)) 2 (cpGen (dd b.1) (hdd b.1))

/-- **The constant summands contribute a root of zero.**  Their line does not
depend on the base point at all. -/
theorem lineEulerOf_vLineY_inl (dd : Fin ℓ → ℕ) (i : Fin 3) :
    lineEulerOf (vLineYBundle (Sum.inl i : Fin 3 ⊕ HBlk dd))
        (fun y => trace_vLineY (Sum.inl i) y) = 0 :=
  lineEulerOf_const _ _ (fun _ _ => rfl)

end

end CharClass
end GroupApproximation
