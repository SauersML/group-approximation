import GroupApproximation.CharClass.CartanEvalMaster
import GroupApproximation.CharClass.CartanEvalCocycle

/-!
# The leftover term is a coboundary

The master identity leaves one term: the functional applied to the homotopy on
the simplicial half of the source differential.  As a function of the simplex
that term is the coboundary of the cochain `σ ↦ ⟨homotopy(e_m ⊗ σ), α⊗β⊗α⊗β⟩`.

The computation is the boundary of a simplex, once: the simplicial half of the
differential is the sum of the faces with the `W`-index kept, both maps in sight
are linear, and summing a cochain over the faces is evaluating its coboundary,
with no signs because `-1 = 1`.

## Main results

* `homCochain` — the homotopy cochain.
* `fourEval_s_wDiffS` — **the leftover term is a coboundary**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation.CharClass

noncomputable section

variable (compB : src singularBoundary ⟶ four)
variable (hzero : ∀ X : TopCat.{0}, (compA.app X).f 0 = (compB.app X).f 0)

/-- The value of the homotopy functional on one generator. -/
noncomputable def homVal (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (n : ℕ) (m : Fin (n + 1)) (τ : singularSimplices X m.val) : ZMod 2 :=
  fourEvalF2 X p q α β (n + 1)
    (((cartanHomotopy compB hzero).s n X).hom
      (Finsupp.single (⟨m, simplexEquiv X m.val τ⟩ : WSIndex n X) (1 : GroupRingZ2)))

/-- **The homotopy cochain**, whose coboundary is the difference of the two
evaluations. -/
noncomputable def homCochain (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (n : ℕ) (m : Fin (n + 1)) : singularCochainGroup (ZMod 2) X m.val :=
  cochainOfFun m.val (homVal compB hzero X p q α β n m)

theorem cochainEval_homCochain (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (n : ℕ) (m : Fin (n + 1)) (τ : singularSimplices X m.val) :
    cochainEval m.val (homCochain compB hzero X p q α β n m) τ
      = fourEvalF2 X p q α β (n + 1)
          (((cartanHomotopy compB hzero).s n X).hom
            (Finsupp.single (⟨m, simplexEquiv X m.val τ⟩ : WSIndex n X) (1 : GroupRingZ2))) := by
  rw [homCochain, cochainEval_cochainOfFun]
  rfl

/-- The simplicial half of the source differential on a generator is the sum of
the faces, with the `W`-index kept. -/
theorem wDiffS_succ_eq_sum (X : TopCat.{0}) (n : ℕ) (m : Fin (n + 1))
    (σ : singularSimplices X (m.val + 1)) :
    wDiffS singularBoundary X n (Fin.succ m) (simplexEquiv X (Fin.succ m).val σ)
      = ∑ j : Fin (m.val + 2),
          Finsupp.single
            (⟨m, simplexEquiv X m.val (faceSimplex X m.val j σ)⟩ : WSIndex n X)
            (1 : GroupRingZ2) := by
  have hbd : singularBoundary.bd X m.val
        (Finsupp.single (simplexEquiv X (m.val + 1) σ) (1 : GroupRingZ2))
      = ∑ j : Fin (m.val + 2),
          Finsupp.single (simplexEquiv X m.val (faceSimplex X m.val j σ))
            (1 : GroupRingZ2) := by
    show Finsupp.mapDomain (simplexEquiv X m.val)
        (bdU GroupRingZ2 X m.val
          (Finsupp.mapDomain (simplexEquiv X (m.val + 1)).symm
            (Finsupp.single (simplexEquiv X (m.val + 1) σ) (1 : GroupRingZ2)))) = _
    rw [Finsupp.mapDomain_single, Equiv.symm_apply_apply, bdU_single,
      Finsupp.mapDomain_finsetSum]
    exact Finset.sum_congr rfl fun j _ => Finsupp.mapDomain_single
  rw [wDiffS_succ]
  show Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (fun τ => (⟨m, τ⟩ : WSIndex n X))
      (singularBoundary.bd X m.val
        (Finsupp.single (simplexEquiv X (m.val + 1) σ) (1 : GroupRingZ2))) = _
  rw [hbd, Finsupp.lmapDomain_apply, Finsupp.mapDomain_finsetSum]
  exact Finset.sum_congr rfl fun j _ => Finsupp.mapDomain_single

/-- **The leftover term of the master identity is a coboundary.** -/
theorem fourEval_s_wDiffS (X : TopCat.{0}) (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (n : ℕ) (m : Fin (n + 1)) (σ : singularSimplices X (m.val + 1)) :
    fourEvalF2 X p q α β (n + 1)
        (((cartanHomotopy compB hzero).s n X).hom
          (wDiffS singularBoundary X n (Fin.succ m)
            (simplexEquiv X (Fin.succ m).val σ)))
      = cochainEval (m.val + 1)
          (cochainCoboundary (ZMod 2) X m.val
            (homCochain compB hzero X p q α β n m)) σ := by
  rw [wDiffS_succ_eq_sum X n m σ]
  refine Eq.trans
    (congrArg (fourEvalF2 X p q α β (n + 1)) (map_sum _ _ Finset.univ)) ?_
  refine Eq.trans (map_sum _ _ Finset.univ) ?_
  have hterm : ∀ j : Fin (m.val + 2),
      fourEvalF2 X p q α β (n + 1)
          (((cartanHomotopy compB hzero).s n X).hom
            (Finsupp.single
              (⟨m, simplexEquiv X m.val (faceSimplex X m.val j σ)⟩ : WSIndex n X)
              (1 : GroupRingZ2)))
        = evAt X m.val (homCochain compB hzero X p q α β n m) m.val
            (faceSimplex X m.val j σ) := by
    intro j
    rw [evAt_self, cochainEval_homCochain]
  refine Eq.trans (Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j) ?_
  refine Eq.trans
    (sum_evAt_face X m.val (homCochain compB hzero X p q α β n m) m.val σ) ?_
  exact evAt_self X (m.val + 1) _ σ

end

end GroupApproximation.CharClass
