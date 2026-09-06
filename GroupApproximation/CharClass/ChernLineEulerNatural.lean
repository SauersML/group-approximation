import GroupApproximation.CharClass.ChernOfInvariance
import GroupApproximation.CharClass.ChernSplitFactor
import GroupApproximation.CharClass.LerayHirschChartClassGen

/-!
# `lineEulerOf` is natural, and normalised

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`lineEulerOf` is `eulerOfBundle` of a line pushed into the `Fin` that `tautEulerOf`
uses, so that the two can be compared without a reindexing.  That convenience makes
its own three basic facts non-trivial, because every one of them changes the index
and so changes the `Fin` size:

* pushing the line along an injection does not change the class -- the two sides sit
  in `Fin`s of unrelated sizes;
* pulling the line back pulls the class back;
* the tautological line of `ℂP^d` has the generator as its class -- here the class is
  taken at `1 + card (Fin (d+1))` while the normalisation `eulerOfBundle_cpTaut` is at
  `d`.

All three are `CPn.eulerOfBundle_pushforward_iso` or its equation-form cousin, which
is exactly what those were built to absorb.

## Main declarations

* `lineEulerOf_pushforward`, `lineEulerOf_comap`, `lineEulerOf_cpTaut`.

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory
open GroupApproximation.CharClass.Bundle
open GroupApproximation.CharClass.CPn

noncomputable section

set_option linter.unusedSectionVars false

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Pushing a line along an injection does not change its Euler class.**  The two
sides are taken at `1 + card κ` and `1 + card ι`, which are unrelated, so this is the
size-free comparison and not `eulerOfBundle_pushforward_congr`. -/
theorem lineEulerOf_pushforward (f : ι → κ) (hf : Function.Injective f)
    (q : Bundle X ι) (hq : ∀ x, (q x).trace = 1) :
    lineEulerOf (pushforward f hf q) (CPn.trace_pushforward_one f hf q hq)
      = lineEulerOf q hq :=
  CPn.eulerOfBundle_pushforward_iso (1 + tautCardOf κ) (1 + tautCardOf ι)
    (by omega) (by omega) (pushforward f hf q) q
    (CPn.trace_pushforward_one f hf q hq) hq
    (BundleIso.symm (pushforwardIso f hf q))
    (tautEmbOf_injective κ) (tautEmbOf_injective ι)

/-- **Naturality.**  Pulling the line back pulls its Euler class back. -/
theorem lineEulerOf_comap (f : C(Y, X)) (q : Bundle X ι)
    (hq : ∀ x, (q x).trace = 1) :
    lineEulerOf (comap f q) (fun y => hq (f y))
      = pull (cmap f) 2 (lineEulerOf q hq) :=
  eulerOfBundle_comap (show 1 ≤ 1 + tautCardOf ι by omega)
    (pushforward (tautEmbOf ι) (tautEmbOf_injective ι) q)
    (CPn.trace_pushforward_one (tautEmbOf ι) (tautEmbOf_injective ι) q hq) f

/-- **Normalisation.**  The tautological line of `ℂP^d` has the degree-two generator
as its Euler class, in the `lineEulerOf` presentation.  The size changes from `d` to
`1 + card (Fin (d+1))`, which the equation form of the descent absorbs. -/
theorem lineEulerOf_cpTaut (d : ℕ) (hd : 1 ≤ d) :
    lineEulerOf (cpTaut d) (trace_cpTaut d) = cpGen d hd :=
  (eulerOfBundle_pushforward_eq_of_bundleIso' d 2 (1 + tautCardOf (Fin (d + 1)))
      (by
        have h : tautCardOf (Fin (d + 1)) = d + 1 := Fintype.card_fin (d + 1)
        omega)
      hd (cpTaut d) (cpTaut d) (BundleIso.refl _) (trace_cpTaut d)
      (tautEmbOf_injective (Fin (d + 1)))
      (CPn.trace_pushforward_one (tautEmbOf (Fin (d + 1)))
        (tautEmbOf_injective (Fin (d + 1))) (cpTaut d) (trace_cpTaut d))).trans
    (eulerOfBundle_cpTaut d hd)

end

end LH
end CharClass
end GroupApproximation
