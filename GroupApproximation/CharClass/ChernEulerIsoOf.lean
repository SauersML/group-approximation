import GroupApproximation.CharClass.ProjectiveSpaceStableOf
import GroupApproximation.CharClass.ChernEulerBundleOf
import GroupApproximation.CharClass.ChernEulerIndex

/-!
# The Euler class over `K` is an invariant of the isomorphism class

The coefficient-generic form of `ChernEulerIso.eulerOfBundle_eq_of_bundleIso` and
`ChernEulerIndex.eulerOfBundle_pushforward_congr`, for any chosen class
`hgen ∈ H^2(ℂP^d; K)`.

Over `F₂` the proof moves the generator up the block inclusion (`pull_cpBlockInclIter_cpGen`).
Over `K` there is no generator to move, and none is needed.  Pullback along the block inclusion is
bijective on `H^2` (`ProjectiveSpaceStableOf.bijective_pull_cpBlockInclIterOf`), so `hgen` is the
pullback of *some* class `H` on the larger projective space.  `cc-bundle`'s rotation homotopy
identifies the two classifying maps after the push.  So the statement holds for every `hgen`, with
no stability hypothesis.

## Main declarations

* `eulerOfBundle_eq_of_bundleIsoOf` — **the Euler class over `K` is an isomorphism invariant**.
* `eulerOfBundle_pushforward_congrOf` — neither the injection nor the representative matters.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open GroupApproximation.STW59
open GroupApproximation.CharClass.Bundle

noncomputable section

/-- **The Euler class over `K` of a line bundle depends only on its isomorphism class**, for any
degree-2 class `hgen` on `ℂP^d` with `d ≥ 1`. -/
theorem eulerOfBundle_eq_of_bundleIsoOf (K : Type) [Field K] {X : Type} [TopologicalSpace X]
    {d : ℕ} (hd : 1 ≤ d) (hgen : Hmod K (CPtop d) 2) (p q : Bundle X (Fin (d + 1)))
    (hp : ∀ x, (p x).trace = 1) (hq : ∀ x, (q x).trace = 1) (e : BundleIso p q) :
    eulerOfBundleOf K hgen p hp = eulerOfBundleOf K hgen q hq := by
  obtain ⟨H, hH⟩ := (bijective_pull_cpBlockInclIterOf K d hd).2 hgen
  have h := pull_eq_of_homotopicOf K
    (f := cmap ((cpBlockInclIter d).comp (classifyOne p hp)))
    (g := cmap ((cpBlockInclIter d).comp (classifyOne q hq)))
    (homotopic_classifyOne_blockInclIter hp hq e) 2 H
  show eulerClassOf K hgen (cmap (classifyOne p hp))
    = eulerClassOf K hgen (cmap (classifyOne q hq))
  rw [eulerClassOf, eulerClassOf, ← hH, ← pull_comp, ← pull_comp]
  exact h

/-- **Neither the injection nor the representative matters**, over `K`.  Both pushforwards are
isomorphic to the same bundle, so this is `eulerOfBundle_eq_of_bundleIsoOf` at the common index with
the two pushforward isomorphisms spliced on. -/
theorem eulerOfBundle_pushforward_congrOf (K : Type) [Field K] {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {N : ℕ} (hN : 1 ≤ N)
    (hgen : Hmod K (CPtop N) 2) (p : Bundle X ι) (q : Bundle X κ)
    {f : ι → Fin (N + 1)} (hf : Function.Injective f)
    {g : κ → Fin (N + 1)} (hg : Function.Injective g)
    (hfp : ∀ x, (pushforward f hf p x).trace = 1)
    (hgq : ∀ x, (pushforward g hg q x).trace = 1)
    (e : BundleIso p q) :
    eulerOfBundleOf K hgen (pushforward f hf p) hfp
      = eulerOfBundleOf K hgen (pushforward g hg q) hgq :=
  eulerOfBundle_eq_of_bundleIsoOf K hN hgen _ _ hfp hgq
    (((pushforwardIso f hf p).symm.trans e).trans (pushforwardIso g hg q))

end

end CPn
end CharClass
end GroupApproximation
