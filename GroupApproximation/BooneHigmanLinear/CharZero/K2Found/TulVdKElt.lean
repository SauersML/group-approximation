import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulVdK
import GroupApproximation.Meta.AxiomGuard

/-!
# `X_{v,w}(1)` is van der Kallen's `X(v, w)` (for H.L1, lane k2-vdk)

For unimodular `v` and `w ⊥ v`, Tulenbaev's `X_{v,w}(u v)` equals `X(v, (u v) w)` (`Xa_eq_E`).
Each canonical piece `pc v w u p q` has two zeros, so `X(v, pc)` is local (`tx_eq_E`), and the
pieces add up to `(u v) w` (`pc_sum_all`) inside the root subgroup of `v` (`E_mul`). In
particular `(tulX r h5).X v w 1 = X(v, w)` (`tulX_X_one`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (U Elements IsUnimodular)

section General

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] (hX : Elements I A)
  [hL : Fact (IsLocal hX)]

/-- `X(v, y) = X_r(v, y)` for unimodular `v` and `y ⊥ v` with two zeros. -/
theorem tx_eq_E {v y : I → A} (hv : IsUnimodular v) (hy : TwoZ y) (hyv : y ⬝ᵥ v = 0) :
    tx hX v y = E hX v y := by
  obtain ⟨r, s, hrs, hr, hs⟩ := hy
  rw [tx_eq hX hr hyv, hL.out v y r s hrs hr hs hyv hv]

#audit_axioms tx_eq_E

theorem coe_prod_txc (h4 : 4 ≤ Fintype.card I) {v : I → A} (hv : IsUnimodular v) (w u : I → A)
    (s : Finset (I × I)) :
    ((∏ pq ∈ s, txc hX (pc_dot v w u pq.1 pq.2) (pc_twoZ h4 v w u pq.1 pq.2) : Cv hX v) :
        SteinbergGroup I A) = E hX v (∑ pq ∈ s, pc v w u pq.1 pq.2) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, OneMemClass.coe_one, E_zero]
  | insert a s ha ih =>
    have hsum : (∑ pq ∈ s, pc v w u pq.1 pq.2) ⬝ᵥ v = 0 := by
      rw [sum_dotProduct]
      exact Finset.sum_eq_zero fun pq _ => pc_dot v w u pq.1 pq.2
    rw [Finset.prod_insert ha, Subgroup.coe_mul, ih, coe_txc, Finset.sum_insert ha,
      tx_eq_E hX hv (pc_twoZ h4 v w u a.1 a.2) (pc_dot v w u a.1 a.2),
      E_mul hX hv (pc_dot v w u a.1 a.2) hsum]

#audit_axioms coe_prod_txc

/-- `X_{v,w}(u v) = X(v, (u v) w)` for unimodular `v` and `w ⊥ v`. -/
theorem Xa_eq_E (h4 : 4 ≤ Fintype.card I) {v w : I → A} (u : I → A) (hv : IsUnimodular v)
    (hw : w ⬝ᵥ v = 0) : Xa hX h4 v w u = E hX v ((u ⬝ᵥ v) • w) := by
  rw [Xa, coe_prod_txc hX h4 hv w u Finset.univ, pc_sum_all u hw]

#audit_axioms Xa_eq_E

end General

section Fin

variable {r : ℕ}

theorem tX_one_eq_elt (E : ∀ (B : Type) [CommRing B], Elements (Fin r) B)
    [∀ (B : Type) [CommRing B], Fact (IsLocal (E B))] (h4 : 4 ≤ Fintype.card (Fin r))
    {B : Type} [CommRing B] {v w : Fin r → B} (h : (v, w) ∈ U (Fin r) B) :
    tX E h4 v w 1 = (E B).elt (v, w) h := by
  obtain ⟨⟨u, hu⟩, hw⟩ := VdK.mem_U.1 h
  have hd : w ∈ Submodule.span B (two0 v) := by
    have e := pc_sum_all u hw
    rw [hu, one_smul] at e
    rw [← e]
    exact Submodule.sum_mem _ fun pq _ =>
      Submodule.subset_span ⟨pc_dot v w u pq.1 pq.2, pc_twoZ h4 v w u pq.1 pq.2⟩
  rw [tX_eq E h4 hd hu, Xa_eq_E (E B) h4 u ⟨u, hu⟩ hw, hu, one_smul, E_of_mem (E B) h]

#audit_axioms tX_one_eq_elt

/-- **`X_{v,w}(1) = X(v, w)`** for k2-vdk's elements (`r ≥ 5`, `(v, w) ∈ U`). -/
theorem tulX_X_one (h5 : 5 ≤ r) {B : Type} [CommRing B] {v w : Fin r → B}
    (h : (v, w) ∈ U (Fin r) B) :
    (tulX r h5).X v w 1 =
      (VdK.elements (Fin r) B (by rw [Fintype.card_fin]; omega)).elt (v, w) h := by
  haveI : ∀ (B : Type) [CommRing B],
      Fact (IsLocal (VdK.elements (Fin r) B (by rw [Fintype.card_fin]; omega))) :=
    fun _ _ => ⟨isLocal_elements _⟩
  exact tX_one_eq_elt (fun B _ => VdK.elements (Fin r) B (by rw [Fintype.card_fin]; omega))
    (card_fin_ge (by omega)) h

#audit_axioms tulX_X_one

end Fin

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
