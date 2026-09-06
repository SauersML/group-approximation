import GroupApproximation.CharClass.SliceVLineRoots
import GroupApproximation.CharClass.SliceRoots

/-!
# The block half of the root family

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`cc-steenrod`'s `vRoot` matches on the block index: zero on the three constant
lines, and on a line of block `(j, i)` the generator of the `j`-th projective
factor pulled back.  `lineEulerOf_vLineY_inl` is the first half.  This file is the
second, stated at `cc-steenrod`'s own names so that their `hroot` is a match on the
block index and nothing else.

`SliceVLineRoots` proves it; this restates it at `baseYFactor` rather than at this
lane's `evalFactor`, which is the same continuous map written twice.  The two spellings
are definitionally equal, so the proof is one application, and having the identity
written down means neither side unfolds the other's definition at the use site.

## Main declarations

* `lineEulerOf_vLineY_inr` — **the block half of `vRoot`.**

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **The block half of the root family.**  The line of block `b` has as its Euler
class the generator of the `b.1`-th projective factor, pulled back along the
projection to that factor.

Only `b.1` is read, so every block over one factor gives the same root; a version
quantified over factors rather than over blocks would be a different theorem, and a
weaker one. -/
theorem lineEulerOf_vLineY_inr (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j)
    (b : HBlk dd) :
    lineEulerOf (vLineYBundle (Sum.inr b : Fin 3 ⊕ HBlk dd))
        (fun y => trace_vLineY (Sum.inr b) y)
      = pull (cmap (baseYFactor dd b.1)) 2 (cpGen (dd b.1) (hdd b.1)) :=
  lineEulerOf_vLineYBundle_inr b (hdd b.1)

end

end LH
end CharClass
end GroupApproximation
