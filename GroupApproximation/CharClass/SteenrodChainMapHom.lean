import GroupApproximation.CharClass.SteenrodChainMap
import GroupApproximation.CharClass.SteenrodTargetLinear
import GroupApproximation.CharClass.CartanSourceBoundary

/-!
# The chain-map condition against the source complex

`SteenrodChainMap.lean` proves the chain-map identity in this lane's own
vocabulary, where a singular simplex is `singularSimplices X n`.  The source
complex of the acyclic-models comparison indexes its basis by the bare hom-set
`stdSimplexTop n ⟶ X` instead, because that is what `FreeOnModels` wants.  The
two differ by exactly one `Equiv.ulift`, `CartanSourceBoundary.simplexEquiv`, and
this file is where it is spent: `PhiHom` is the diagonal read on the hom-set
basis, and `dTgt_PhiHom` is the chain-map condition against `wDiff` itself.

Nothing above this file carries the `ULift`, and nothing below it needs to.

## Main results

* `PhiHom` — Steenrod's diagonal as a `Λ`-linear map `W ⊗ S(X) → S(X) ⊗ S(X)`,
  on the source carrier `WTensorSMod`.
* `PhiHom_wDiffW`, `PhiHom_wDiffS` — its value on each half of the source
  differential.
* `dTgt_PhiHom` — **the chain-map condition**, in the form the comparison
  consumes.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial SimplexCategory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

namespace GroupApproximation
namespace CharClass
namespace Steenrod

noncomputable section

/-! ## 1. The diagonal on the hom-set basis -/

/-- A basis element of the source, read in this lane's vocabulary. -/
def wsOfHom (X : TopCat.{0}) (k : ℕ)
    (b : Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X) : WSIndex X k :=
  ⟨b.1, (simplexEquiv X b.1.val).symm b.2⟩

/-- **Steenrod's diagonal on the source complex.**  The `Λ`-linear extension from
the hom-set basis of `W ⊗ S(X)`. -/
noncomputable def PhiHom (X : TopCat.{0}) (k : ℕ) :
    WTensorSMod X k →ₗ[GroupRingZ2] (PairIdx X k →₀ ZMod 2) :=
  Finsupp.linearCombination GroupRingZ2
    (fun b : Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X => phiPair X k (wsOfHom X k b))

theorem PhiHom_single (X : TopCat.{0}) (k : ℕ)
    (b : Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X) (c : GroupRingZ2) :
    PhiHom X k (Finsupp.single b c) = c • phiPair X k (wsOfHom X k b) := by
  unfold PhiHom
  simp

theorem singularBoundary_bd (X : TopCat.{0}) (n : ℕ) :
    singularBoundary.bd X n = bdHom GroupRingZ2 X n := rfl

/-! ## 2. The two halves of the source differential -/

/-- On the `(1 + t)` half, `Φ` gives `Φ(e_{i-1} ⊗ σ) + T Φ(e_{i-1} ⊗ σ)`. -/
theorem PhiHom_wDiffW (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2))
    (φ : stdSimplexTop n.val ⟶ X) :
    PhiHom X k (wDiffW X k n φ) = phiOfW X k n ((simplexEquiv X n.val).symm φ) := by
  revert φ
  induction n using Fin.lastCases with
  | last =>
      intro φ
      rw [wDiffW_last, phiOfW_last]
      exact map_zero (PhiHom X k)
  | cast j =>
      intro φ
      rw [wDiffW_castSucc, phiOfW_castSucc, map_smul, PhiHom_single, one_smul,
        one_add_gen_smul]
      rfl

/-- On the boundary half, `Φ` gives the sum of `Φ(e_i ⊗ ∂_j σ)`. -/
theorem PhiHom_wDiffS (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2))
    (φ : stdSimplexTop n.val ⟶ X) :
    PhiHom X k (wDiffS singularBoundary X k n φ)
      = phiOfS X k n ((simplexEquiv X n.val).symm φ) := by
  revert φ
  induction n using Fin.cases with
  | zero =>
      intro φ
      rw [wDiffS_zero, phiOfS_zero]
      exact map_zero (PhiHom X k)
  | succ m =>
      intro φ
      have hbd : singularBoundary.bd X m.val (Finsupp.single φ (1 : GroupRingZ2))
          = ∑ i : Fin (m.val + 2),
              Finsupp.single
                (simplexEquiv X m.val
                  (faceSimplex X m.val i ((simplexEquiv X (m.val + 1)).symm φ)))
                (1 : GroupRingZ2) := by
        rw [singularBoundary_bd, bdHom_apply, Finsupp.mapDomain_single, bdU_single,
          mapDomain_finset_sum]
        exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_single
      rw [wDiffS_succ, phiOfS_succ, hbd, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, PhiHom_single]
      exact one_smul _ _

/-- `Φ` on a whole generator of the source differential. -/
theorem PhiHom_wDiffGen (X : TopCat.{0}) (k : ℕ) (n : Fin (k + 2))
    (φ : stdSimplexTop n.val ⟶ X) :
    PhiHom X k (wDiffGen singularBoundary X k n φ)
      = phiOfW X k n ((simplexEquiv X n.val).symm φ)
        + phiOfS X k n ((simplexEquiv X n.val).symm φ) := by
  rw [wDiffGen, map_add, PhiHom_wDiffW, PhiHom_wDiffS]

/-! ## 3. The chain-map condition -/

theorem dTgt_PhiHom_single (X : TopCat.{0}) (k : ℕ)
    (b : Σ n : Fin (k + 2), stdSimplexTop n.val ⟶ X) :
    dTgt X (ZMod 2) k (PhiHom X (k + 1) (Finsupp.single b 1))
      = PhiHom X k (wDiff singularBoundary X k (Finsupp.single b 1)) := by
  rw [PhiHom_single, one_smul, wDiff_single, PhiHom_wDiffGen]
  exact dTgt_phiPair X k b.1 ((simplexEquiv X b.1.val).symm b.2)

/-- **Steenrod's diagonal is a chain map.**  `∂ ∘ Φ = Φ ∘ d`, with `d` the
differential of `W ⊗ S(X)` and `∂` the differential of `S(X) ⊗ S(X)`. -/
theorem dTgt_PhiHom (X : TopCat.{0}) (k : ℕ) (y : WTensorSMod X (k + 1)) :
    dTgt X (ZMod 2) k (PhiHom X (k + 1) y) = PhiHom X k (wDiff singularBoundary X k y) := by
  classical
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · simp
  · intro u v hu hv
    rw [map_add, map_add, hu, hv, map_add]
    exact (map_add (PhiHom X k) _ _).symm
  · intro b c
    have hs : (Finsupp.single b c : WTensorSMod X (k + 1))
        = c • Finsupp.single b (1 : GroupRingZ2) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hs, map_smul, dTgt_smul, map_smul, map_smul]
    exact congrArg (fun z => c • z) (dTgt_PhiHom_single X k b)

/-- The chain-map condition as an equality of `Λ`-linear maps. -/
theorem dTgtLin_comp_PhiHom (X : TopCat.{0}) (k : ℕ) :
    (dTgtLin X k).comp (PhiHom X (k + 1))
      = (PhiHom X k).comp (wDiff singularBoundary X k) :=
  LinearMap.ext (fun y => dTgt_PhiHom X k y)

end

end Steenrod
end CharClass
end GroupApproximation
