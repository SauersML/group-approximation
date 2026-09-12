import GroupApproximation.CharClass.OddPShufflePrimRoot
import GroupApproximation.CharClass.OddPTupleFunctor
import GroupApproximation.CharClass.OddPEval
import GroupApproximation.Meta.AxiomGuard

/-!
# The slot permutation `σ_r`, for the bad-residue vanishing

The vanishing theorem V (`OddPCartanVanish.lean`) compares two natural chain maps
`W ⊗ C(X) → C(X)^{⊗p}` that are linear over `F_p[ℤ/p]` when the generator acts on the target as
`T ^ r`.  The first is the equivariant diagonal followed by the signed slot permutation
`σ_r = tupPerm (mulPerm p r hr)⁻¹`.  This file collects the three tuple-level facts about `σ_r`
that comparison uses:

* `tupPerm_mulPerm_inv_tupT` — `σ_r ∘ T = T ^ r ∘ σ_r`, from lx-redpow's
  `tupT_pow_mul_tupPerm_mulPerm_inv`;
* `tupMap_tupPerm` — the pushforward commutes with every signed slot permutation;
* `tupEval_tupPerm_const` — a constant tuple of cochains concentrated in one EVEN degree does not
  see a slot permutation, since on its support every Koszul exponent is a sum of products of even
  numbers.
-/

namespace GroupApproximation.CharClass

open CategoryTheory
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

namespace OddPCartanVanish

section Tuple

variable (K : Type) [CommRing K] (X : TopCat.{0}) {r : ℕ}

/-- **The pushforward commutes with every signed slot permutation.** -/
theorem tupMap_tupPerm {Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (π : Equiv.Perm (Fin r))
    (x : tupMod K X r k) :
    tupMap K f r k (tupPerm K X r k π x) = tupPerm K Y r k π (tupMap K f r k x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | single t c =>
    have h : tupMap K f r k (tupPerm K X r k π (Finsupp.single t (1 : K)))
        = tupPerm K Y r k π (tupMap K f r k (Finsupp.single t (1 : K))) := by
      rw [tupPerm_single, map_smul, tupMap_single, tupMap_single, tupPerm_single]
      rfl
    rw [← Finsupp.smul_single_one, map_smul, map_smul, h, map_smul, map_smul]

/-- **A constant tuple of single-degree cochains in an even degree does not see a slot
permutation.** -/
theorem tupEval_tupPerm_const (π : Equiv.Perm (Fin r)) (φ : ∀ n : ℕ, singularCochainGroup K X n)
    (q : ℕ) (hqe : Even q) (hq : ∀ n, n ≠ q → φ n = 0) (k : ℕ) (x : tupMod K X r k) :
    tupEval K X r k (fun _ => φ) (tupPerm K X r k π x) = tupEval K X r k (fun _ => φ) x := by
  have hL : (tupEval K X r k (fun _ => φ)).comp (tupPerm K X r k π)
      = tupEval K X r k (fun _ => φ) := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext_ring
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [tupPerm_single, map_smul, tupEval_single, tupEval_single, smul_eq_mul, permTupIdx_val]
    have hre : ∏ j, tagEvalG K φ (permTup π t.1 j) = ∏ j, tagEvalG K φ (t.1 j) :=
      Equiv.prod_comp π (fun j => tagEvalG K φ (t.1 j))
    rw [hre]
    by_cases hall : ∀ l, (t.1 l).1 = q
    · have h2 : permExp X π t.1
          = 2 * ∑ i : Fin r, ∑ j : Fin r, if i < j ∧ π j < π i then q / 2 * q else 0 := by
        unfold permExp
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hall]
        split_ifs
        · obtain ⟨c, hc⟩ := hqe
          rw [hc, show (c + c) / 2 = c by omega]
          ring
        · rfl
      have hexp : Even (permExp X π t.1) := ⟨_, h2.trans (two_mul _)⟩
      rw [hexp.neg_one_pow, one_mul]
    · obtain ⟨l, hl⟩ := not_forall.mp hall
      have h0 : ∏ j, tagEvalG K φ (t.1 j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ l) (tagEvalG_of_eq_zero K φ (t.1 l) (hq _ hl))
      rw [h0, mul_zero]
  exact LinearMap.congr_fun hL x

end Tuple

/-- **`σ_r = tupPerm (mulPerm p r hr)⁻¹` intertwines `T` with `T ^ r`**, in every degree and at
every space (lx-redpow's `tupT_pow_mul_tupPerm_mulPerm_inv`). -/
theorem tupPerm_mulPerm_inv_tupT (p r : ℕ) (hr : Nat.Coprime r p) (X : TopCat.{0}) (k : ℕ)
    (y : tupMod (ZMod p) X p k) :
    tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹ (tupT (ZMod p) X p k y)
      = (tupT (ZMod p) X p k ^ r) (tupPerm (ZMod p) X p k (mulPerm p r hr)⁻¹ y) := by
  have h := LinearMap.congr_fun (tupT_pow_mul_tupPerm_mulPerm_inv (ZMod p) X k r hr) y
  simp only [Module.End.mul_apply] at h
  exact h.symm

end OddPCartanVanish

end

end GroupApproximation.CharClass
