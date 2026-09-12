import GroupApproximation.CharClass.ChernEulerCastSucc
import GroupApproximation.CharClass.BundlePushforward

/-!
# The Euler class across index sizes

`eulerOfBundle` is defined only for a bundle indexed by `Fin (d+1)`, because it
goes through a classifying map to `ℂP^d`.  The bundles the Leray–Hirsch chart step
compares are not of that shape: the tautological line of `P(p ⊕ 1)` is indexed by
`ι ⊕ Unit`, and the tautological line of `ℂP¹` by `Fin 2`.  A `BundleIso` between
them exists — `cc-bundle`'s `tautLineIsoCPOne` — and it crosses index types, which
is exactly what `BundleIso` was built to allow.

So the Euler class of a bundle over an arbitrary finite index is *defined* by
pushing it into a `Fin`, and the two facts a consumer needs are here:

* the choice of injection does not matter, and neither does the bundle within its
  isomorphism class (`eulerOfBundle_pushforward_congr`);
* pushing a bundle that was already `Fin (a+1)`-indexed along `iterFin` returns its
  own Euler class (`eulerOfBundle_pushforward_iterFin`), so the big-index class can
  be read back down.

`eulerOfBundle_pushforward_eq_of_bundleIso` combines them into the one statement the
chart step calls: a bundle pushed into a large index has the Euler class of
anything `Fin`-indexed it is isomorphic to.  No generator computation appears on the
`ι` side, because the class there is *defined* by the pushforward; the descent is
`ProjectiveSpaceIterate`'s, already proved.

## Main declarations

* `iterFin_injective` — the iterated successor is injective.
* `eulerOfBundle_pushforward_congr` — index and representative are immaterial.
* `eulerOfBundle_pushforward_iterFin` — the descent to the small index.
* `eulerOfBundle_pushforward_eq_of_bundleIso` — **the workhorse**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open GroupApproximation.CharClass.Bundle

noncomputable section

/-! ## 1. Two small facts -/

theorem iterFin_injective (d k : ℕ) : Function.Injective (iterFin d k) := by
  intro i j h
  have hi := iterFin_val d k i
  have hj := iterFin_val d k j
  rw [h, hj] at hi
  exact Fin.val_injective (by omega)

/-- The pushforward of a line is a line. -/
theorem trace_pushforward_one {X : Type} [TopologicalSpace X] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (f : ι → κ)
    (hf : Function.Injective f)
    (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1) (x : X) :
    (pushforward f hf p x).trace = 1 :=
  (trace_pushforward f hf p x).trans (hp x)

/-! ## 2. Independence of the injection and of the representative -/

/-- **Neither the injection nor the representative matters.**  Both pushforwards are
isomorphic to the same bundle, so this is `eulerOfBundle_eq_of_bundleIso` at the
common index with the two pushforward isomorphisms spliced on. -/
theorem eulerOfBundle_pushforward_congr {X : Type} [TopologicalSpace X]
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {N : ℕ} (hN : 1 ≤ N)
    (p : Bundle X ι) (q : Bundle X κ)
    {f : ι → Fin (N + 1)} (hf : Function.Injective f)
    {g : κ → Fin (N + 1)} (hg : Function.Injective g)
    (hfp : ∀ x, (pushforward f hf p x).trace = 1)
    (hgq : ∀ x, (pushforward g hg q x).trace = 1)
    (e : BundleIso p q) :
    eulerOfBundle hN (pushforward f hf p) hfp
      = eulerOfBundle hN (pushforward g hg q) hgq :=
  eulerOfBundle_eq_of_bundleIso hN _ _ hfp hgq
    (((pushforwardIso f hf p).symm.trans e).trans (pushforwardIso g hg q))

/-! ## 3. The descent to the small index -/

/-- **Pushing a `Fin (a+1)`-indexed bundle along `iterFin` returns its own Euler
class.**  The classifying map of the pushforward is the original followed by the
iterated coordinate embedding, and that embedding fixes the generator. -/
theorem eulerOfBundle_pushforward_iterFin {X : Type} [TopologicalSpace X]
    (a k : ℕ) (ha : 1 ≤ a) (p : Bundle X (Fin (a + 1))) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (pushforward (iterFin a k) (iterFin_injective a k) p x).trace = 1) :
    eulerOfBundle (show 1 ≤ a + k by omega)
        (pushforward (iterFin a k) (iterFin_injective a k) p) hq
      = eulerOfBundle ha p hp := by
  show eulerClass (cpGen (a + k) (show 1 ≤ a + k by omega))
      (cmap (classifyOne (pushforward (iterFin a k) (iterFin_injective a k) p) hq))
    = eulerClass (cpGen a ha) (cmap (classifyOne p hp))
  rw [classifyOne_pushforward p hp (iterFin_injective a k) hq,
    cpEmbed_congr _ (iterMat_isometry a k) (iterMat_eq_coordIncl a k).symm]
  exact eulerClass_cpEmbed_iterMat a k ha (cmap (classifyOne p hp))

/-! ## 4. The workhorse -/

/-- **A bundle pushed into a large index has the Euler class of anything
`Fin`-indexed it is isomorphic to.**

This is the form the Leray–Hirsch chart step calls with `p` the tautological line
of `P(q ⊕ 1)`, indexed by `ι ⊕ Unit`, and `q` the tautological line of `ℂP¹`,
indexed by `Fin 2`. -/
theorem eulerOfBundle_pushforward_eq_of_bundleIso {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] [DecidableEq ι] (a k : ℕ) (ha : 1 ≤ a)
    (p : Bundle X ι) (q : Bundle X (Fin (a + 1))) (e : BundleIso p q)
    (hq : ∀ x, (q x).trace = 1)
    {f : ι → Fin (a + k + 1)} (hf : Function.Injective f)
    (hfp : ∀ x, (pushforward f hf p x).trace = 1) :
    eulerOfBundle (show 1 ≤ a + k by omega) (pushforward f hf p) hfp
      = eulerOfBundle ha q hq := by
  rw [eulerOfBundle_pushforward_congr (show 1 ≤ a + k by omega) p q hf
    (iterFin_injective a k) hfp
    (trace_pushforward_one (iterFin a k) (iterFin_injective a k) q hq) e]
  exact eulerOfBundle_pushforward_iterFin a k ha q hq _

end

end CPn
end CharClass
end GroupApproximation
