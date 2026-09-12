import GroupApproximation.CharClass.OddPEval
import GroupApproximation.CharClass.OddPTupleFunctor

/-!
# Naturality of the tensor evaluation

`tupEval_tupMap`: pushing a tuple forward along `f : X ⟶ Y` and evaluating cochains on `Y` is
evaluating their pullbacks on `X`.  One slot at a time this is the vendored
`cochainPullback_eval`, whose simplex `(TopCat.toSSet.map f).app _ σ` is `pushSimplex f n σ` by
definition, so the product over the slots is reindexed by nothing.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (K : Type) [CommRing K] {X Y : TopCat.{0}} {r : ℕ}

/-- One slot: a pushed simplex evaluates against a cochain as the simplex against its pullback. -/
theorem tagEvalG_tagPush (f : X ⟶ Y) (ψ : ∀ n : ℕ, singularCochainGroup K Y n) (τ : TagSimp X) :
    tagEvalG K ψ (tagPush f τ) = tagEvalG K (fun n => cochainPullback f n (ψ n)) τ :=
  (cochainPullback_eval f τ.1 (ψ τ.1) τ.2).symm

/-- **(E7) Naturality of the evaluation.** -/
theorem tupEval_tupMap (f : X ⟶ Y) (φ : Fin r → ∀ n : ℕ, singularCochainGroup K Y n) (k : ℕ)
    (x : tupMod K X r k) :
    tupEval K Y r k φ (tupMap K f r k x)
      = tupEval K X r k (fun j n => cochainPullback f n (φ j n)) x := by
  have hL : (tupEval K Y r k φ).comp (tupMap K f r k)
      = tupEval K X r k (fun j n => cochainPullback f n (φ j n)) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [tupMap_single, tupEval_single, tupEval_single]
    exact Finset.prod_congr rfl fun j _ => tagEvalG_tagPush K f (φ j) (t.1 j)
  exact LinearMap.congr_fun hL x

#audit_axioms tupEval_tupMap

end

end GroupApproximation.CharClass
