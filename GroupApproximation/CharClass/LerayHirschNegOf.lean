import GroupApproximation.CharClass.LerayHirschDegree

/-!
# Leray–Hirsch does not see the sign of the class

Over `F₂` the tautological class and its dual are the same element.  Over a coefficient ring `K`
they differ by a sign (`LH.tautEulerDualK = −LH.tautEulerOfK`), and the splitting principle is
stated with the dual one.  So Leray–Hirsch for one has to give Leray–Hirsch for the other, and it
does for any class: `(−ξ)^i = (−1)^i ξ^i`, so the combination of `−ξ` is the combination of `ξ`
on the signed family, and the sign change of the family is an involution.

## Main declarations

* `cupPowE_neg` — the cup powers of `−e` are the signed cup powers of `e`.
* `lhMap_neg` — the combination of `−ξ` on a family is that of `ξ` on the signed family.
* `lerayHirschGraded_neg` — **Leray–Hirsch for `ξ` gives Leray–Hirsch for `−ξ`**.
-/

set_option autoImplicit false

namespace GroupApproximation
namespace CharClass
namespace LH

open CategoryTheory

noncomputable section

variable {K : Type} [CommRing K] {X P : TopCat.{0}}

/-- **The cup powers of `−e` are the signed cup powers of `e`.** -/
theorem cupPowE_neg (e : Hmod K P 2) (m : ℕ) :
    cupPowE (-e) m = ((-1 : K) ^ m) • cupPowE e m := by
  induction m with
  | zero => simp only [cupPowE_zero, pow_zero, one_smul]
  | succ m ih =>
    rw [cupPowE_succ, cupPowE_succ, ih, cup_smul_left, ← neg_one_smul K e, cup_smul_right,
      smul_smul, pow_succ]

/-- **The Leray–Hirsch combination of `−ξ` is the combination of `ξ` on the signed family.** -/
theorem lhMap_neg (π : P ⟶ X) (ξ : Hmod K P 2) (r n : ℕ)
    (a : (i : Fin (lhDomainCard r n)) → Hmod K X (n - 2 * (i : ℕ))) :
    lhMap π (-ξ) r n a = lhMap π ξ r n (fun i => ((-1 : K) ^ (i : ℕ)) • a i) := by
  simp only [lhMap]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cupPowE_neg, cup_smul_right, pull_smul, cup_smul_left]

/-- **Leray–Hirsch for `ξ` gives Leray–Hirsch for `−ξ`**, over any coefficient ring. -/
theorem lerayHirschGraded_neg {π : P ⟶ X} {ξ : Hmod K P 2} {r : ℕ}
    (L : LerayHirschGraded π ξ r) : LerayHirschGraded π (-ξ) r := by
  refine ⟨fun n => ?_⟩
  have hsgn : Function.Bijective
      (fun (a : (i : Fin (lhDomainCard r n)) → Hmod K X (n - 2 * (i : ℕ)))
        (i : Fin (lhDomainCard r n)) => ((-1 : K) ^ (i : ℕ)) • a i) := by
    refine Function.Involutive.bijective fun a => funext fun i => ?_
    show ((-1 : K) ^ (i : ℕ)) • ((-1 : K) ^ (i : ℕ)) • a i = a i
    rw [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  have hfun : lhMap π (-ξ) r n
      = lhMap π ξ r n ∘
          (fun (a : (i : Fin (lhDomainCard r n)) → Hmod K X (n - 2 * (i : ℕ)))
            (i : Fin (lhDomainCard r n)) => ((-1 : K) ^ (i : ℕ)) • a i) :=
    funext fun a => lhMap_neg π ξ r n a
  rw [hfun]
  exact (L.bij n).comp hsgn

end

end LH
end CharClass
end GroupApproximation
