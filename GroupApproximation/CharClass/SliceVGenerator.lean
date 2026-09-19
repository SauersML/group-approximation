import GroupApproximation.CharClass.SliceVLineRoots

/-!
# The generator of a projective factor, stated once

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`Wu.lix_stepD_closed` and `KnTwo.ChernSliceValue` both take a family
`gen : Fin ℓ → TotalH (KnTwo.YTop (baseY dd))` of generators of the projective
factors, and `SliceVLineRoots` shows the roots of `V` are exactly those classes,
`dd j` of them over the factor `j`.

The generator is written down once here so that the two consumers cite a term
rather than a description.  A second spelling of it would be the failure mode
where both sides are green about different classes.

## Main declarations

* `sliceGen` — **the generator of the `j`-th factor.**
* `sliceGen_eq_root` — every block line over that factor has it as its class.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

set_option linter.unusedSectionVars false

variable {ℓ : ℕ} {dd : Fin ℓ → ℕ}

/-- **The generator of the `j`-th projective factor**, as an element of the total
cohomology ring of the base: the degree-two generator of `ℂP^{dd j}` pulled back
along the projection to that factor. -/
def sliceGen (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) (j : Fin ℓ) :
    TotalH (KnTwo.YTop (baseY dd)) :=
  TotalH.of (KnTwo.YTop (baseY dd)) 2
    (pull (cmap (evalFactor dd j)) 2 (cpGen (dd j) (hdd j)))

/-- **Every block line over the factor `j` has that generator as its class.**  The
block index only records *which* copy, so the `dd j` blocks over one factor all
contribute the same generator, and the slice polynomial sees it with multiplicity
`dd j`. -/
theorem sliceGen_eq_root (dd : Fin ℓ → ℕ) (hdd : ∀ j, 0 < dd j) (β : HBlk dd) :
    TotalH.of (KnTwo.YTop (baseY dd)) 2
        (lineEulerOf (vLineYBundle (Sum.inr β)) (trace_vLineY (Sum.inr β)))
      = sliceGen dd hdd β.1 :=
  congrArg (TotalH.of (KnTwo.YTop (baseY dd)) 2)
    (lineEulerOf_vLineYBundle_inr β (hdd β.1))

end

end LH
end CharClass
end GroupApproximation
