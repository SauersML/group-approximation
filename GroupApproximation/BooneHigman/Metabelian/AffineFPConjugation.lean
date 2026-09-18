import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Algebra.Group.Equiv.TypeTags
import GroupApproximation.BooneHigman.Metabelian.AffineFPTranslations

/-!
# Commutation and conjugation of the translations `y_i(r)` (lane bh-met-05)

Research node `affine-extension-of-fp-elementary-group-is-fp-proof`, steps F3 and F4
(`research/artifacts/bh-sl3-zt-host-2026-09-12.md`, §2).  Under `AffineRel S x τ`:

* `yi_commute` (F3): `y_i(r)` and `y_j(s)` commute for `i ≠ j` (for `i = j` this is additivity);
* `conj_yi_ne`, `conj_yi_same` (F4): `x a b r'` fixes `y_i(r)` when `b ≠ i`, and
  `x a i r' · y_i(r) · (x a i r')⁻¹ = y_i(r) · y_a(r' r)`, matching `x_{ai}(r') (r e_i)`;
* `zHom`: the homomorphism `R^I → P`, `v ↦ ∏ y_i(v_i)`, with `zHom_single`.
-/

namespace GroupApproximation
namespace BooneHigman
namespace Metabelian
namespace AffineFP

open scoped commutatorElement

namespace AffineRel

variable {I R P : Type*} [CommRing R] [Group P] {S : Set R}
  {x : ∀ i j : I, i ≠ j → R → P} {τ : I → P}

/-- Step F3: translations in different coordinates commute. -/
theorem yi_commute (hR : AffineRel S x τ) (i j : I) (_hij : i ≠ j) (r s : R) :
    Commute (hR.yi i r) (hR.yi j s) := by
  obtain ⟨k, hki, hkj, -⟩ := hR.four i j j
  obtain ⟨k', hk'i, hk'j, hk'k⟩ := hR.four i j k
  rw [hR.yi_eq i k hki.symm r, hR.yi_eq j k' hk'j.symm s]
  have hc : Commute (x j k' hk'j.symm s) ⁅x i k hki.symm r, τ k⁆ :=
    commute_commutator_of (hR.comm j k' i k hk'j.symm hki.symm hk'i hkj s r)
      (hR.commute_x_tau s j k' hk'j.symm k hk'k.symm)
  exact commute_commutator_of hc.symm (hR.commute_tau_y i k hki.symm r k').symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yi_commute

/-- Step F4, first case: `x a b r'` fixes `y_i(r)` when `b ≠ i`. -/
theorem conj_yi_ne (hR : AffineRel S x τ) (a b : I) (hab : a ≠ b) (i : I) (hbi : b ≠ i)
    (r' r : R) : Commute (x a b hab r') (hR.yi i r) := by
  obtain ⟨k, hki, hka, hkb⟩ := hR.four i a b
  rw [hR.yi_eq i k hki.symm r]
  exact commute_commutator_of (hR.comm a b i k hab hki.symm hbi hka r' r)
    (hR.commute_x_tau r' a b hab k hkb)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.conj_yi_ne

/-- Step F4, second case: `x a i r' · y_i(r) · (x a i r')⁻¹ = y_i(r) · y_a(r' r)`. -/
theorem conj_yi_same (hR : AffineRel S x τ) (a i : I) (hai : a ≠ i) (r' r : R) :
    x a i hai r' * hR.yi i r * (x a i hai r')⁻¹ = hR.yi i r * hR.yi a (r' * r) := by
  obtain ⟨k, hki, hka, -⟩ := hR.four i a a
  obtain ⟨k', hk'i, hk'a, hk'k⟩ := hR.four i a k
  have hc : Commute (x a k hka.symm (r' * r)) ⁅x i k' hk'i.symm r, τ k'⁆ :=
    commute_commutator_of (hR.comm a k i k' hka.symm hk'i.symm hki hk'a (r' * r) r)
      (hR.commute_x_tau (r' * r) a k hka.symm k' hk'k)
  have e1 : x a i hai r' * x i k hki.symm r * (x a i hai r')⁻¹ =
      x a k hka.symm (r' * r) * x i k hki.symm r :=
    hR.conj_x_right a i k hai hki.symm hka.symm r' r
  have e2 : x a i hai r' * τ k * (x a i hai r')⁻¹ = τ k :=
    (hR.commute_x_tau r' a i hai k hki).mul_inv_cancel
  rw [hR.yi_eq i k hki.symm r, hR.yi_eq a k hka.symm (r' * r), conjugate_commutatorElement,
    e1, e2, commutatorElement_mul_left_eq_conj_mul,
    hR.yk_indep i k k' hki.symm hk'i.symm r, hc.mul_inv_cancel]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.conj_yi_same

/-- The homomorphisms `yiHom i` pairwise commute. -/
theorem yiHom_commute (hR : AffineRel S x τ) :
    Pairwise fun i j : I => ∀ (a : Multiplicative R) (b : Multiplicative R),
      Commute (hR.yiHom i a) (hR.yiHom j b) := by
  intro i j hij a b
  exact hR.yi_commute i j hij (Multiplicative.toAdd a) (Multiplicative.toAdd b)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.yiHom_commute

section Fintype

variable [Fintype I] [DecidableEq I]

/-- The homomorphism `R^I → P`, `v ↦ ∏ᵢ y_i(v_i)`. -/
noncomputable def zHom (hR : AffineRel S x τ) : Multiplicative (I → R) →* P :=
  (MonoidHom.noncommPiCoprod (fun i => hR.yiHom i) hR.yiHom_commute).comp
    (MulEquiv.piMultiplicative fun _ : I => R).toMonoidHom

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.zHom

theorem zHom_single (hR : AffineRel S x τ) (i : I) (r : R) :
    hR.zHom (Multiplicative.ofAdd (Pi.single i r)) = hR.yi i r := by
  have e : MulEquiv.piMultiplicative (fun _ : I => R) (Multiplicative.ofAdd (Pi.single i r)) =
      Pi.mulSingle i (Multiplicative.ofAdd r) := by
    funext j
    by_cases hj : j = i
    · rw [hj]
      change Multiplicative.ofAdd (Pi.single i r i) = _
      rw [Pi.single_eq_same, Pi.mulSingle_eq_same]
    · change Multiplicative.ofAdd (Pi.single i r j) = _
      rw [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, ofAdd_zero]
  change MonoidHom.noncommPiCoprod (fun i => hR.yiHom i) hR.yiHom_commute
    (MulEquiv.piMultiplicative (fun _ : I => R) (Multiplicative.ofAdd (Pi.single i r))) = _
  rw [e]
  exact MonoidHom.noncommPiCoprod_mulSingle (fun i => hR.yiHom i) i (Multiplicative.ofAdd r)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.AffineFP.AffineRel.zHom_single

end Fintype

end AffineRel

end AffineFP
end Metabelian
end BooneHigman
end GroupApproximation
