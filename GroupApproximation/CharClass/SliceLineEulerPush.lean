import GroupApproximation.CharClass.ChernEulerPushforwardSize
import GroupApproximation.CharClass.ChernSplitFactor

/-!
# Pushing a line into a larger index does not move its Euler class

The slice equation puts `V` in a block of a doubled index, on the nose, so the
lines of the restricted mapping torus are this lane's lines pushed along the
second-summand inclusion.  Their Euler classes have to be the same, and they are
not the same *term*: `lineEulerOf` embeds into a `Fin` whose length is read off
the index type, and the two index types have different cardinalities.

`cc-projective`'s `eulerOfBundle_pushforward_iso` is exactly the statement that
closes that gap, at an arbitrary injection and with the two target sizes
unrelated, so this file is one application of it.  Nothing here is fitted to the
second-summand inclusion.

## Main declarations

* `lineEulerOf_pushforward` — **the Euler class survives a change of index.**
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass

open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn
open GroupApproximation.CharClass.LH

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **A line pushed along any injection has the same Euler class.**  The two
`lineEulerOf` terms embed into `Fin`s of different lengths, so this is not a
definitional matter; it is `cc-projective`'s size-independent comparison. -/
theorem lineEulerOf_pushforward {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (L : Bundle X ι) (hL : ∀ x, (L x).trace = 1)
    (u : ι → κ) (hu : Function.Injective u) :
    lineEulerOf (pushforward u hu L) (trace_pushforward_one u hu L hL)
      = lineEulerOf L hL :=
  eulerOfBundle_pushforward_iso (1 + tautCardOf κ) (1 + tautCardOf ι)
    (by omega) (by omega) (pushforward u hu L) L
    (trace_pushforward_one u hu L hL) hL (pushforwardIso u hu L).symm
    (tautEmbOf_injective κ) (tautEmbOf_injective ι)

end

end CharClass
end GroupApproximation
