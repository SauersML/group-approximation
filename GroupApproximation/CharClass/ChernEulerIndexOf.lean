import GroupApproximation.CharClass.ChernEulerEmbedOf
import GroupApproximation.CharClass.ChernEulerIsoOf

/-!
# The Euler class over `K` across index sizes

The coefficient-generic form of `ChernEulerIndex` §3–4.  `eulerOfBundleOf K hgen` is defined
only for a bundle indexed by `Fin (N+1)`, relative to a class `hgen ∈ H^2(ℂP^N; K)`, and the chart
step of Leray–Hirsch compares a line pushed into a large index with a line indexed by a small
`Fin (a+1)`.

Over `F₂` the descent to the small index returns the Euler class with the canonical generator.
Over `K` the class moves with the map: pushing along `iterFin a k` is the same as pulling `hgen`
back along the iterated coordinate embedding, and the small-index Euler class is taken relative to
that restricted class.  It is nonzero when `hgen` is (`pull_cpEmbed_iterMat_ne_zeroOf`).

## Main declarations

* `eulerOfBundle_pushforward_iterFinOf` — the descent to the small index.
* `eulerOfBundle_pushforward_eq_of_bundleIsoOf` — **the workhorse over `K`**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **Pushing a `Fin (a+1)`-indexed line along `iterFin` returns its own Euler class, relative to
the restricted class.**  The classifying map of the pushforward is the original followed by the
iterated coordinate embedding, and composing with the embedding pulls `hgen` back. -/
theorem eulerOfBundle_pushforward_iterFinOf (K : Type) [CommRing K] (a k : ℕ)
    (hgen : Hmod K (CPtop (a + k)) 2) (p : Bundle X (Fin (a + 1))) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (pushforward (iterFin a k) (iterFin_injective a k) p x).trace = 1) :
    eulerOfBundleOf K hgen (pushforward (iterFin a k) (iterFin_injective a k) p) hq
      = eulerOfBundleOf K
          (pull (cmap (cpEmbed (iterMat a k) (iterMat_isometry a k))) 2 hgen) p hp := by
  show eulerClassOf K hgen
      (cmap (classifyOne (pushforward (iterFin a k) (iterFin_injective a k) p) hq))
    = eulerClassOf K (pull (cmap (cpEmbed (iterMat a k) (iterMat_isometry a k))) 2 hgen)
        (cmap (classifyOne p hp))
  rw [classifyOne_pushforward p hp (iterFin_injective a k) hq,
    cpEmbed_congr _ (iterMat_isometry a k) (iterMat_eq_coordIncl a k).symm]
  exact eulerClassOf_cpEmbed_iterMat K a k hgen (cmap (classifyOne p hp))

/-- **A line pushed into a large index has the Euler class of anything `Fin`-indexed it is
isomorphic to, relative to the restricted class**, over a field `K` and for every `hgen`. -/
theorem eulerOfBundle_pushforward_eq_of_bundleIsoOf (K : Type) [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] (a k : ℕ) (ha : 1 ≤ a) (hgen : Hmod K (CPtop (a + k)) 2)
    (p : Bundle X ι) (q : Bundle X (Fin (a + 1))) (e : BundleIso p q)
    (hq : ∀ x, (q x).trace = 1)
    {f : ι → Fin (a + k + 1)} (hf : Function.Injective f)
    (hfp : ∀ x, (pushforward f hf p x).trace = 1) :
    eulerOfBundleOf K hgen (pushforward f hf p) hfp
      = eulerOfBundleOf K
          (pull (cmap (cpEmbed (iterMat a k) (iterMat_isometry a k))) 2 hgen) q hq := by
  rw [eulerOfBundle_pushforward_congrOf K (show 1 ≤ a + k by omega) hgen p q hf
    (iterFin_injective a k) hfp
    (trace_pushforward_one (iterFin a k) (iterFin_injective a k) q hq) e]
  exact eulerOfBundle_pushforward_iterFinOf K a k hgen q hq _

end

end CPn
end CharClass
end GroupApproximation
