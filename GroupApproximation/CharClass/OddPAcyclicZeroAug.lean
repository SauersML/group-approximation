import GroupApproximation.CharClass.OddPAcyclicZero
import GroupApproximation.CharClass.OddPTupleFunctor

/-!
# Degree zero on the models, against `tupAug`

Lane `lix-cupone`, block `OddPAcyclic*`, export (E0) in the spelling `lix-steenrod`'s
`OddPTupleFunctor` consumes: the augmentation is `tupAug K X r = Finsupp.linearCombination K 1`, so
this is `OddPAcyclicZero.tupD_exists_preimage_zero_of_sum_stdSimplexTop` read through that
definition.  Kept in its own file so that the proof does not wait on `OddPTupleFunctor`'s closure.
-/

namespace GroupApproximation.CharClass

/-- **(E0) An augmentation cycle of the degree-`0` tuple carrier over a standard simplex is a
boundary.** -/
theorem tupD_exists_preimage_zero_stdSimplexTop (K : Type) [Field K] (n r : ℕ)
    (y : tupMod K (stdSimplexTop n) r 0) (hy : tupAug K (stdSimplexTop n) r y = 0) :
    ∃ z : tupMod K (stdSimplexTop n) r 1, tupD K (stdSimplexTop n) r 0 z = y :=
  tupD_exists_preimage_zero_of_sum_stdSimplexTop K n r y hy

end GroupApproximation.CharClass
