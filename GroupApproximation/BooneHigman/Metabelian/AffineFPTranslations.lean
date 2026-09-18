import GroupApproximation.BooneHigman.Metabelian.AffineFPRelations

/-!
# The translation elements `y_i(r)` (lane bh-met-05)

Research node `affine-extension-of-fp-elementary-group-is-fp-proof`, step F
(`research/artifacts/bh-sl3-zt-host-2026-09-12.md`, §2).  Under `AffineRel S x τ` put
`y_i(r) = ⁅x i k r, τ k⁆` for any `k ≠ i`.

* `yk_mul_neg` (F1): `⁅x i k r, τ k⁆ ⁅x i k' (-r), τ k'⁆ = 1` for distinct `i, k, k'`;
* `yk_indep`: the commutator does not depend on `k` (this uses four indices);
* `yi`, `yi_eq`: the element `y_i(r)`, and its value at any `k ≠ i`;
* `yi_add` (F2), `yi_zero`, `yi_one` (`y_i(1) = τ i`), and the homomorphism `yiHom`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace AffineFP

open scoped commutatorElement

namespace AffineRel

variable {I R P : Type*} [CommRing R] [Group P] {S : Set R}
  {x : ∀ i j : I, i ≠ j → R → P} {τ : I → P}

/-- Step F1: `⁅x i k r, τ k⁆ ⁅x i k' (-r), τ k'⁆ = 1` for distinct `i, k, k'`. -/
theorem yk_mul_neg (hR : AffineRel S x τ) (i k k' : I) (hik : i ≠ k) (hik' : i ≠ k')
    (hkk' : k ≠ k') (r : R) :
    ⁅x i k hik r, τ k⁆ * ⁅x i k' hik' (-r), τ k'⁆ = 1 := by
  have e := mul_commutator_eq_one (u := x k k' hkk' 1)
    (hR.commute_x_tau r i k hik k' hkk'.symm)
    (hR.conj_x_left i k k' hik hkk' hik' r 1)
    (hR.c2 k k' hkk')
    (hR.comm i k' i k hik' hik hik'.symm hik.symm (r * 1) r).inv_left
    (hR.commute_x_tau (r * 1) i k' hik' k hkk').inv_left
    (hR.commute_tau_y i k hik r k')
  rwa [mul_one, ← hR.x_neg] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yk_mul_neg

/-- The commutator `⁅x i k r, τ k⁆` does not depend on the auxiliary index `k ≠ i`. -/
theorem yk_indep (hR : AffineRel S x τ) (i k k' : I) (hik : i ≠ k) (hik' : i ≠ k')
    (r : R) : ⁅x i k hik r, τ k⁆ = ⁅x i k' hik' r, τ k'⁆ := by
  by_cases hkk : k = k'
  · subst hkk
    rfl
  · obtain ⟨m, hmi, hmk, hmk'⟩ := hR.four i k k'
    exact mul_right_cancel ((hR.yk_mul_neg i k m hik hmi.symm hmk.symm r).trans
      (hR.yk_mul_neg i k' m hik' hmi.symm hmk'.symm r).symm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yk_indep

/-- A chosen index different from `i`. -/
noncomputable def kOf (hR : AffineRel S x τ) (i : I) : I :=
  (hR.four i i i).choose

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.kOf

theorem kOf_ne (hR : AffineRel S x τ) (i : I) : i ≠ hR.kOf i :=
  (hR.four i i i).choose_spec.1.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.kOf_ne

/-- The translation element `y_i(r) = ⁅x i k r, τ k⁆`. -/
noncomputable def yi (hR : AffineRel S x τ) (i : I) (r : R) : P :=
  ⁅x i (hR.kOf i) (hR.kOf_ne i) r, τ (hR.kOf i)⁆

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yi

theorem yi_eq (hR : AffineRel S x τ) (i k : I) (hik : i ≠ k) (r : R) :
    hR.yi i r = ⁅x i k hik r, τ k⁆ :=
  hR.yk_indep i (hR.kOf i) k (hR.kOf_ne i) hik r

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yi_eq

/-- Step F2 at explicit auxiliary indices. -/
theorem y_add (hR : AffineRel S x τ) (i k k' : I) (hik : i ≠ k) (hik' : i ≠ k')
    (hkk' : k ≠ k') (r s : R) :
    ⁅x i k hik (r + s), τ k⁆ = ⁅x i k hik r, τ k⁆ * ⁅x i k' hik' s, τ k'⁆ := by
  have hY : ⁅x i k hik s, τ k⁆ = ⁅x i k' hik' s, τ k'⁆ := hR.yk_indep i k k' hik hik' s
  have hc : Commute (x i k hik r) ⁅x i k' hik' s, τ k'⁆ :=
    commute_commutator_of (hR.comm i k i k' hik hik' hik.symm hik'.symm r s)
      (hR.commute_x_tau r i k hik k' hkk'.symm)
  have hd : Commute ⁅x i k' hik' s, τ k'⁆ ⁅x i k hik r, τ k⁆ :=
    commute_commutator_of hc.symm (hR.commute_tau_y i k' hik' s k).symm
  rw [hR.add i k hik r s, commutatorElement_mul_left_eq_conj_mul, hY, hc.mul_inv_cancel]
  exact hd.eq

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.y_add

/-- Step F2: `y_i` is additive. -/
theorem yi_add (hR : AffineRel S x τ) (i : I) (r s : R) :
    hR.yi i (r + s) = hR.yi i r * hR.yi i s := by
  obtain ⟨k', hk'i, hk'k, -⟩ := hR.four i (hR.kOf i) i
  rw [hR.yi_eq i k' hk'i.symm s]
  exact hR.y_add i (hR.kOf i) k' (hR.kOf_ne i) hk'i.symm hk'k.symm r s

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yi_add

theorem yi_zero (hR : AffineRel S x τ) (i : I) : hR.yi i 0 = 1 := by
  rw [yi, hR.x_zero, commutatorElement_one_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yi_zero

/-- `y_i(1) = τ i`. -/
theorem yi_one (hR : AffineRel S x τ) (i : I) : hR.yi i 1 = τ i := by
  rw [yi, commutatorElement_def, hR.c2, (hR.c3 (hR.kOf i) i).mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yi_one

/-- The homomorphism `r ↦ y_i(r)`. -/
noncomputable def yiHom (hR : AffineRel S x τ) (i : I) : Multiplicative R →* P where
  toFun r := hR.yi i (Multiplicative.toAdd r)
  map_one' := hR.yi_zero i
  map_mul' a b := hR.yi_add i (Multiplicative.toAdd a) (Multiplicative.toAdd b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yiHom

theorem yiHom_apply (hR : AffineRel S x τ) (i : I) (r : R) :
    hR.yiHom i (Multiplicative.ofAdd r) = hR.yi i r :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yiHom_apply

end AffineRel

end AffineFP
end Metabelian
end BooneHigman
end GroupApproximation
