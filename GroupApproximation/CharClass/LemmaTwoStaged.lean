import GroupApproximation.CharClass.LemmaTwoStepDLix
import GroupApproximation.CharClass.LemmaTwoGlue

/-!
# The endgame, staged over its remaining inputs

Lane `cc-lix-odd`.

`CharClass/LemmaTwoClosed.lean` is deliberately **absent** until it carries no hypotheses;
this file is its content with every remaining input named, so that the final theorem is one
substitution when the last of them lands.

The two arithmetic side conditions of the tower are **not** hypotheses: `LIX.lixDD_pos` and
`LIX.even_lixDD` are theorems, so positivity and evenness at every stage are discharged
here.  Those were the two places where the final instantiation could have failed after
everything else was green, since Step D runs on evenness.

## The hypotheses, and who owns each

* `chern` — the degreewise mod-2 Chern classes of a projection-model bundle, at every
  stage of the tower (`cc-projective`).
* `hC` — the space-independent Cartan formula (`cc-cartan`, via `cc-wu`).
* `chain` — Step C's odd side per mapping torus, in the `ThomChainThom` shape
  (`cc-thom` and `cc-projective`, behind the Thom class datum).
* `data` — Step D's even side per mapping torus, in the `WuStepDLix` shape, whose one open
  field is the Chern splitting (`cc-projective`).

## Main result

* `lemmaTwoHolds_staged` — **`LIX.LemmaTwoHolds`**, over those four.
-/

noncomputable section

namespace GroupApproximation.CharClass

open scoped Matrix
open GroupApproximation.STW59

set_option linter.unusedSectionVars false

/-- **The endpoint's proposition, over the four remaining inputs.**

When the last of them lands this becomes `CharClass.lemmaTwoHolds` with no hypotheses, and
`cs-endpoint`'s held file applies it unchanged. -/
theorem lemmaTwoHolds_staged
    (chern : ∀ j : ℕ, LixChernDeg (LIX.lixDD j))
    (hC : Wu.CartanTotal)
    (chain : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
        ThomChainThom (LIX.lixDD j)
          (chern j (mappingTorus Vmat G circHoriz circHeight)
            (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
            (lixRank (LIX.lixDD j))))
    (data : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ),
        Continuous G → (∀ m, IsCornerUnitary (Vmat m) (G m)) →
        WuStepDLix (LIX.lixDD j)
          (lixChernOf (chern j) (mappingTorus Vmat G circHoriz circHeight))) :
    LIX.LemmaTwoHolds :=
  lemmaTwoHolds_of fun j =>
    lemmaTwoInput_lix (chern j) (fun i => LIX.lixDD_pos j i) hC
      (fun i => LIX.even_lixDD j i) (chain j) (data j)

end GroupApproximation.CharClass
