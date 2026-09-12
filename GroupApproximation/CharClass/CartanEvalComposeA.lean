import GroupApproximation.CharClass.CartanEvalAW
import GroupApproximation.CharClass.CartanComposeA

/-!
# Evaluating the first composite

Composite A is `(Φ₀ ⊗ Φ₀) ∘ Φ`.  Pairing its value against `α, β, α, β` is
pairing `Φ`'s value against `α ⌣ β` in both slots, because each `Φ₀` turns a
pair of cochains into their cup product; and pairing `Φ` against two cochains is
evaluating their cup-`i` product.

So the first composite evaluates to `(α ⌣ β) ⌣ᵢ (α ⌣ β)`, which is the left-hand
side of the Cartan formula: the cochain whose class is `Sqⁿ` of the cup product.

The total degree is forced.  Two cochains of degree `p + q` pair against a
bidegree of the tensor square only in degree `(p + q) + (p + q)`, so `k` is twice
the degree of the product, and the simplex degree `n` and the cup index `k - n`
are what the Steenrod square construction uses.

## Main results

* `fourEvalF2_tenHom_awHom` — the `Φ₀ ⊗ Φ₀` step.
* `fourEvalF2_compA_phiPair` — **composite A evaluated**.
-/

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

namespace GroupApproximation.CharClass

noncomputable section

variable {X : TopCat.{0}} (p q : ℕ)
  (α : singularCochainGroup (ZMod 2) X p) (β : singularCochainGroup (ZMod 2) X q)

theorem awHom_f (X : TopCat.{0}) (a : ℕ) : (awHom X).f a = Steenrod.awDiag X a := rfl

/-- **The `Φ₀ ⊗ Φ₀` step.**  Pairing four cochains against the image of
`Φ₀ ⊗ Φ₀` is pairing their two cup products against the pair itself. -/
theorem fourEvalF2_tenHom_awHom (k : ℕ) (y : Steenrod.PairIdx X k →₀ ZMod 2) :
    fourEvalF2 X p q α β k (tenHom (awHom X) (awHom X) k y)
      = pairEvalIdx X (p + q) (p + q) (cochainCup p q α β) (cochainCup p q α β) k y := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]
  | single w c =>
      obtain ⟨⟨⟨a, b⟩, hab⟩, σ, τ⟩ := w
      rw [pairEvalIdx_single]
      have hs : (Finsupp.single (⟨⟨(a, b), hab⟩, (σ, τ)⟩ : Steenrod.PairIdx X k) c)
          = c • Finsupp.single (⟨⟨(a, b), hab⟩, (σ, τ)⟩ : Steenrod.PairIdx X k)
              (1 : ZMod 2) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hs, map_smul, map_smul, smul_eq_mul,
        ← tenElt_single_single (singFreeCx X) (singFreeCx X)
          (⟨(a, b), hab⟩ : Steenrod.PairDeg k) σ τ,
        tenHom_tenElt, awHom_f, awHom_f, Steenrod.awDiag_single, Steenrod.awDiag_single,
        one_smul, one_smul, fourEvalF2_tenElt_pair,
        pairEvalIdx_phiZero_eq_evAt, pairEvalIdx_phiZero_eq_evAt]
      rfl

/-- **Composite A evaluated.**  Pairing `α, β, α, β` against `(Φ₀ ⊗ Φ₀)(Φ(e_i ⊗ σ))`
is evaluating the cup-`i` square of `α ⌣ β` on `σ`. -/
theorem fourEvalF2_compA_phiPair (k : ℕ) (hk : p + q + (p + q) = k)
    (n : Fin (k + 1)) (σ : singularSimplices X n.val) :
    fourEvalF2 X p q α β k
        (tenHom (awHom X) (awHom X) k (Steenrod.phiPair X k ⟨n, σ⟩))
      = cochainEval n.val
          (cochainCupI (k - n.val) (p + q) (p + q) n.val
            (cochainCup p q α β) (cochainCup p q α β)) σ := by
  rw [fourEvalF2_tenHom_awHom p q α β k,
    pairEvalIdx_phiPair k n (p + q) (p + q) hk
      (cochainCup p q α β) (cochainCup p q α β) σ]

end

end GroupApproximation.CharClass
