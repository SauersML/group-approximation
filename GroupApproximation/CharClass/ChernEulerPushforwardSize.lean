import GroupApproximation.CharClass.ChernEulerIndex

/-!
# The Euler class does not see the size of the index it is pushed into

Lane `cc-projective` of the STW Problem LIX program
(`notes/LIX_FULL_PROGRAM_2026-09-05.md`, §1.4, item 5).

`CharClass/ChernEulerIndex.lean` proves that the Euler class of a line does not
depend on which injection it is pushed along, and that pushing a `Fin (a+1)`-indexed
line further along `iterFin` returns its own class.  Both fix the target size.  What
is missing, and what a comparison of two bundles with *different* index types needs,
is that the size does not matter either.

The obstruction is arithmetic rather than geometric: `M + N` and `N + M` are not the
same term, so a proof that lifts both sides to a common `Fin` by the same device
lands them in two different types.  The fix is the one this lane already uses for
`eulerOfBundle_pushforward_eq_of_bundleIso'`: give the common size as an **equation**
`a + k = N` rather than definitionally, and discharge it by `subst` inside the proof.
Then the caller instantiates the equation both ways round and `omega` does the work.

## Main declarations

* `eulerOfBundle_pushforward_size` — the size of the target does not matter.
* `eulerOfBundle_pushforward_iso` — **isomorphic lines pushed into unrelated index
  sizes have the same Euler class.**

## Manuscript status

Machinery.  Certifies no manuscript step on its own.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace CPn

open CategoryTheory
open GroupApproximation.CharClass.Bundle

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The target size does not matter.**  Two pushforwards of one line into `Fin (a+1)`
and into `Fin (N+1)`, along any two injections, have the same Euler class.

The size is given by the equation `a + k = N` rather than as `a + k`, because the
callers need it instantiated both ways round and truncated subtraction makes the
definitional form unusable.  `subst` removes it in one step. -/
theorem eulerOfBundle_pushforward_size {ι : Type} [Fintype ι] [DecidableEq ι]
    (a k N : ℕ) (hNa : a + k = N) (ha : 1 ≤ a)
    (p : Bundle X ι) (hp : ∀ x, (p x).trace = 1)
    {f : ι → Fin (a + 1)} (hf : Function.Injective f)
    {F : ι → Fin (N + 1)} (hF : Function.Injective F) :
    eulerOfBundle (show 1 ≤ N by omega) (pushforward F hF p)
        (trace_pushforward_one F hF p hp)
      = eulerOfBundle ha (pushforward f hf p) (trace_pushforward_one f hf p hp) := by
  subst hNa
  have hcomp : Function.Injective (iterFin a k ∘ f) := (iterFin_injective a k).comp hf
  have hstep : eulerOfBundle (show 1 ≤ a + k by omega) (pushforward F hF p)
      (trace_pushforward_one F hF p hp)
      = eulerOfBundle (show 1 ≤ a + k by omega) (pushforward (iterFin a k ∘ f) hcomp p)
        (trace_pushforward_one _ hcomp p hp) :=
    eulerOfBundle_pushforward_congr (show 1 ≤ a + k by omega) p p hF hcomp
      (trace_pushforward_one F hF p hp) (trace_pushforward_one _ hcomp p hp)
      (BundleIso.refl p)
  have hlift : eulerOfBundle (show 1 ≤ a + k by omega)
      (pushforward (iterFin a k ∘ f) hcomp p) (trace_pushforward_one _ hcomp p hp)
      = eulerOfBundle (show 1 ≤ a + k by omega)
        (pushforward (iterFin a k) (iterFin_injective a k) (pushforward f hf p))
        (trace_pushforward_one _ (iterFin_injective a k) _
          (trace_pushforward_one f hf p hp)) :=
    eulerOfBundle_pushforward_congr (show 1 ≤ a + k by omega) p (pushforward f hf p)
      hcomp (iterFin_injective a k) (trace_pushforward_one _ hcomp p hp)
      (trace_pushforward_one _ (iterFin_injective a k) _
        (trace_pushforward_one f hf p hp))
      (pushforwardIso f hf p)
  exact hstep.trans (hlift.trans
    (eulerOfBundle_pushforward_iterFin a k ha (pushforward f hf p)
      (trace_pushforward_one f hf p hp) _))

/-- **Isomorphic lines pushed into unrelated index sizes have the same Euler class.**

This is the comparison two bundles with different index types need, and the reason
`eulerOfBundle_pushforward_congr` is not enough on its own: that lemma requires both
pushforwards to land in the same `Fin`, which is exactly what fails when the two
index types have different cardinalities.  Both sides are lifted to `Fin (M+N+1)`,
where the injection no longer matters. -/
theorem eulerOfBundle_pushforward_iso {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (p : Bundle X ι) (q : Bundle X κ) (hp : ∀ x, (p x).trace = 1)
    (hq : ∀ x, (q x).trace = 1) (e : BundleIso p q)
    {f : ι → Fin (M + 1)} (hf : Function.Injective f)
    {g : κ → Fin (N + 1)} (hg : Function.Injective g) :
    eulerOfBundle hM (pushforward f hf p) (trace_pushforward_one f hf p hp)
      = eulerOfBundle hN (pushforward g hg q) (trace_pushforward_one g hg q hq) := by
  have hF : Function.Injective (iterFin M N ∘ f) := (iterFin_injective M N).comp hf
  have hG : Function.Injective
      (Fin.castLE (show N + 1 ≤ M + N + 1 by omega) ∘ g) :=
    (Fin.castLE_injective _).comp hg
  have hleft := eulerOfBundle_pushforward_size M N (M + N) rfl hM p hp hf hF
  have hright := eulerOfBundle_pushforward_size N M (M + N) (by omega) hN q hq hg hG
  have hmid : eulerOfBundle (show 1 ≤ M + N by omega)
      (pushforward (iterFin M N ∘ f) hF p) (trace_pushforward_one _ hF p hp)
      = eulerOfBundle (show 1 ≤ M + N by omega)
        (pushforward (Fin.castLE (show N + 1 ≤ M + N + 1 by omega) ∘ g) hG q)
        (trace_pushforward_one _ hG q hq) :=
    eulerOfBundle_pushforward_congr (show 1 ≤ M + N by omega) p q hF hG
      (trace_pushforward_one _ hF p hp) (trace_pushforward_one _ hG q hq) e
  exact hleft.symm.trans (hmid.trans hright)

end

end CPn
end CharClass
end GroupApproximation
