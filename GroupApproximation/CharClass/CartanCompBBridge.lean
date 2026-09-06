import GroupApproximation.CharClass.CartanEvalComposeB
import GroupApproximation.CharClass.CartanEvalBasis
import GroupApproximation.CharClass.SteenrodFourfoldBPackage
import GroupApproximation.CharClass.SteenrodFourfoldAgree

/-!
# Composite B, packaged, meets the evaluated comparison

The comparison is stated on composite B as a natural transformation applied to a
basis element of the source; the evaluation is stated on its value at a
generator.  This file crosses between them, and supplies the degree-zero
agreement in the shape the comparison wants.

The two first composites are the same map on the nose: both are `Φ₀ ⊗ Φ₀`
composed with `Φ`, and the structures carrying them differ only in proof fields.

## Main results

* `compB_single_eq` — composite B on a basis element.
* `compA_eq_compBNat_zero` — the degree-zero agreement.
* `fourEvalF2_compBGen'` — composite B evaluated, with the total degree carried
  as a parameter rather than spelled as a sum.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

/-- Composite B on a basis element of the source is its value at the matching
resolution index. -/
theorem compB_single_eq (X : TopCat.{0}) (k : ℕ) (i : Fin (k + 1))
    (τ : singularSimplices X i.val) :
    ((Steenrod.compBNat.app X).f k).hom
        (Finsupp.single (⟨i, simplexEquiv X i.val τ⟩ : WSIndex k X) (1 : GroupRingZ2))
      = Steenrod.compBGen X k (k - i.val) τ := by
  show Steenrod.compB X k
      (Finsupp.single (⟨i, simplexEquiv X i.val τ⟩ :
        Σ n : Fin (k + 1), stdSimplexTop n.val ⟶ X) (1 : GroupRingZ2)) = _
  rw [Steenrod.compB_single, one_smul, Equiv.symm_apply_apply]

/-- **The degree-zero agreement.**  The two first composites are the same map. -/
theorem compA_eq_compBNat_zero (X : TopCat.{0}) :
    (compA.app X).f 0 = (Steenrod.compBNat.app X).f 0 := by
  apply ModuleCat.hom_ext
  show compAHom X 0 = Steenrod.compB X 0
  exact Steenrod.compA_eq_compB_zero X

/-- Composite B evaluated, with the total degree a parameter. -/
theorem fourEvalF2_compBGen' {X : TopCat.{0}} (p q : ℕ)
    (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)
    (k i N : ℕ) (hk : N + i = k) (σ : singularSimplices X N) :
    fourEvalF2 X p q α β k (Steenrod.compBGen X k i σ)
      = ∑ j ∈ Finset.range (i + 1),
          evAt X (p + p - j + (q + q - (i - j)))
            (cochainCup (p + p - j) (q + q - (i - j))
              (cochainCupI j p p (p + p - j) α α)
              (cochainCupI (i - j) q q (q + q - (i - j)) β β)) N σ := by
  subst hk
  exact fourEvalF2_compBGen p q α β i σ

end

end GroupApproximation.CharClass
