import GroupApproximation.CharClass.SliceValueV

/-!
# Lemma 2 over Step C alone

`cc-steenrod`'s `vSliceValue_sliceGen` closes the even side's last input, so the
whole of Lemma 2 now rests on `cc-thom`'s Step C chain and nothing else.  This file
is that substitution and nothing more.

Why it is one line: the even side was already assembled over `VSliceValue` at
`cc-projective`'s `sliceGen`, which is the term their theorem is stated at, so no
bridge, no transport and no existential introduction stands between the two.  The
comparison that made that true was done before their theorem existed, which is why
it costs nothing now.

The dimension positivity `sliceGen` asks for is `LIX.lixDD_pos`, a theorem about
the tower, and the compactness and non-emptiness of the projective base are
instances.  So the substitution carries no side condition of its own.

## Main declarations

* `lemmaTwoHolds_of_chain` — **`LIX.LemmaTwoHolds` over Step C alone.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open CategoryTheory
open scoped Matrix
open GroupApproximation.STW59

noncomputable section

set_option linter.unusedSectionVars false

/-- **Lemma 2 over Step C alone.**  The even side is discharged: the splitting
principle, the splitting of the Chern classes, the slice identification and the
value of the classes on the slice are all theorems now.  What remains is
`cc-thom`'s odd side, per stage and per mapping torus. -/
theorem lemmaTwoHolds_of_chain
    (chain : ∀ j : ℕ,
      ∀ (G : baseM (LIX.lixDD j) → Matrix (VIdx (LIX.lixDD j)) (VIdx (LIX.lixDD j)) ℂ)
        (hGc : Continuous G) (hGu : ∀ m, IsCornerUnitary (Vmat m) (G m)),
        (∀ m, G m *ᵥ Sum.elim (aVec m) 0 = Sum.elim (bVec m) 0) →
        ThomChainThom (LIX.lixDD j)
          (lixChern (LIX.lixDD j) (mappingTorus Vmat G circHoriz circHeight)
            (continuous_mappingTorus_lix hGc) (isStarProjection_mappingTorus_lix hGu)
            (lixRank (LIX.lixDD j)))) :
    LIX.LemmaTwoHolds :=
  lemmaTwoHolds_of_sliceGen chain
    (fun j => vSliceValue_sliceGen (LIX.lixDD j) (LIX.lixDD_pos j))

/-! ## The axiom report -/

#print axioms lemmaTwoHolds_of_chain

end

end CharClass
end GroupApproximation
