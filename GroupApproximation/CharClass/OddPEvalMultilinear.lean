import GroupApproximation.CharClass.OddPEval

/-!
# The tensor evaluation is linear in each slot

(E8) `tupEval_add_slot` and `tupEval_smul_slot`: replacing slot `j`'s graded cochain by a sum or a
scalar multiple distributes over the evaluation, which is what additivity of the operations
(plan §5.3) consumes.  On a basis tuple both are the single slot identity times the product of the
untouched slots, `tupEval_single_update`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

variable (K : Type) [CommRing K] {X : TopCat.{0}} {r : ℕ}

theorem tagEvalG_add (ψ₁ ψ₂ : ∀ n : ℕ, singularCochainGroup K X n) (τ : TagSimp X) :
    tagEvalG K (ψ₁ + ψ₂) τ = tagEvalG K ψ₁ τ + tagEvalG K ψ₂ τ := by
  unfold tagEvalG
  rw [Pi.add_apply, cochainEval_add]

theorem tagEvalG_smul (c : K) (ψ : ∀ n : ℕ, singularCochainGroup K X n) (τ : TagSimp X) :
    tagEvalG K (c • ψ) τ = c * tagEvalG K ψ τ := by
  unfold tagEvalG
  rw [Pi.smul_apply, cochainEval_smul]

/-- On a basis tuple, the evaluation with slot `j` replaced is that slot's value times the product
of the other slots. -/
theorem tupEval_single_update (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (j : Fin r)
    (ψ : ∀ n : ℕ, singularCochainGroup K X n) {k : ℕ} (t : TupIdx X r k) :
    tupEval K X r k (Function.update φ j ψ) (Finsupp.single t 1)
      = tagEvalG K ψ (t.1 j) * ∏ l ∈ Finset.univ.erase j, tagEvalG K (φ l) (t.1 l) := by
  rw [tupEval_single]
  exact oddPEval_prod_split
    (fun l => tagEvalG K (Function.update φ j ψ l) (t.1 l))
    (fun l => tagEvalG K (φ l) (t.1 l)) j (tagEvalG K ψ (t.1 j))
    (congrArg (fun ψ' => tagEvalG K ψ' (t.1 j)) (Function.update_self j _ φ))
    (fun l hl => congrArg (fun ψ' => tagEvalG K ψ' (t.1 l)) (Function.update_of_ne hl _ φ))

/-- **(E8) Additivity in one slot.** -/
theorem tupEval_add_slot (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (j : Fin r)
    (ψ₁ ψ₂ : ∀ n : ℕ, singularCochainGroup K X n) (k : ℕ) (x : tupMod K X r k) :
    tupEval K X r k (Function.update φ j (ψ₁ + ψ₂)) x
      = tupEval K X r k (Function.update φ j ψ₁) x + tupEval K X r k (Function.update φ j ψ₂) x := by
  have hL : tupEval K X r k (Function.update φ j (ψ₁ + ψ₂))
      = tupEval K X r k (Function.update φ j ψ₁) + tupEval K X r k (Function.update φ j ψ₂) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply]
    rw [tupEval_single_update, tupEval_single_update, tupEval_single_update, tagEvalG_add, add_mul]
  exact LinearMap.congr_fun hL x

/-- **(E8) Homogeneity in one slot.** -/
theorem tupEval_smul_slot (φ : Fin r → ∀ n : ℕ, singularCochainGroup K X n) (j : Fin r) (c : K)
    (ψ : ∀ n : ℕ, singularCochainGroup K X n) (k : ℕ) (x : tupMod K X r k) :
    tupEval K X r k (Function.update φ j (c • ψ)) x
      = c * tupEval K X r k (Function.update φ j ψ) x := by
  have hL : tupEval K X r k (Function.update φ j (c • ψ))
      = c • tupEval K X r k (Function.update φ j ψ) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.smul_apply]
    rw [tupEval_single_update, tupEval_single_update, tagEvalG_smul, smul_eq_mul, mul_assoc]
  rw [LinearMap.congr_fun hL x, LinearMap.smul_apply, smul_eq_mul]

#audit_axioms tupEval_add_slot
#audit_axioms tupEval_smul_slot

end

end GroupApproximation.CharClass
