import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJResStep
import GroupApproximation.Meta.AxiomGuard

/-!
# The residual root check, part 4: the checks of `x_mL(c)`, `x_jL(c)`, and one reduction

Lane `bh-met-94e`.  Notation of `ElemFPK2PolyNagaoJResStep`; everything is under `Low D`.

* `k2PolyNagaoJRes_Ck_xmL`: the check of `x_mL(c)` at supported `u` with `deg u_j < D`:
  `x_mL(c) = W⁻¹ (W x_mL(c) W⁻¹) W` with `W x_mL(c) W⁻¹ ∈ V` (`k2PolyNagaoJRes_Ck_conj`).
* `k2PolyNagaoJRes_Ck_xjL`: the check of `x_jL(c)` at supported `z` with `deg z_m < D`:
  `x_jL(c) = ω⁻¹ x_mL(c) ω` (the Weyl trick), and `(ω z)_j = -z_m`.
* `k2PolyNagaoJRes_y_conj`: `y = A⁻¹ (C y) A` for `A = x_jm(q)`, `C = x_jL(q)`.
* `k2PolyNagaoJRes_caseB`: the check of `y` at supported `v` with
  `deg (v_j % v_m) < D` and `deg (v_m + v_L) < D`.  With `A = x_jm(-(v_j / v_m)) ∈ S` and
  `C = x_jL(-(v_j / v_m))`, `y = A⁻¹ (C y) A`; `(A v)_j = v_j % v_m` and
  `(y A v)_m = v_m + v_L`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act unitVec)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- **The check of `x_mL(c)`** under `Low D`, at `u` supported on `{m, L, j}`,
`deg u_j < D`. -/
theorem k2PolyNagaoJRes_Ck_xmL {K : Finset I} {m L j : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m) (hj : j ∈ K.erase m) {D : WithBot ℕ}
    (hLow : k2PolyNagaoJRes_Low p K m L hmL j D) (c : Polynomial (ZMod p))
    {u : I → Polynomial (ZMod p)} (hu : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = u)
    (hS : k2PolyNagaoJRes_Sj m L j u) (hd : (u j).degree < D) :
    k2PolyNagaoJRes_Ck p K m L hmL (x m L hmL c) u := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hWG := k2PolyNagaoJRes_W_mem_G (p := p) (K := K) hmL hmK
  have hxG := k2PolyEuclid_x_mem_G (K := K) hmL c (Finset.mem_insert_of_mem hmK)
    (Finset.mem_insert_self L K)
  have hd' : (act (x m L hmL c) u j).degree < D := by
    rw [k2PolyNagaoWide_act_x_ne hmL c u hjm]
    exact hd
  refine k2PolyNagaoJRes_Ck_conj (A := w m L hmL (1 : (Polynomial (ZMod p))ˣ))
    (B := w m L hmL (1 : (Polynomial (ZMod p))ˣ) * x m L hmL c *
      (w m L hmL (1 : (Polynomial (ZMod p))ˣ))⁻¹) (by group)
    (k2PolyNagaoJRes_Ck_W hmL hmK hLK hthird hStab hj hLow hu hS hd) ?_
    (k2PolyNagaoJRes_Ck_W hmL hmK hLK hthird hStab hj hLow (k2PolyNF_orbit_act hxG hu)
      (k2PolyNagaoJRes_Sj_x hmL (Or.inl rfl) c hS) hd')
  exact k2PolyNagaoJRes_Ck_Q hmL hmK hLK hthird hStab
    (k2PolyNagaoJRes_W_conj_mem_Q hmL hmK hthird c) (k2PolyNF_orbit_act hWG hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Ck_xmL

/-- **The check of `x_jL(c)`** under `Low D`, at `z` supported on `{m, L, j}`,
`deg z_m < D` (the Weyl trick `x_jL(c) = ω⁻¹ x_mL(c) ω`). -/
theorem k2PolyNagaoJRes_Ck_xjL {K : Finset I} {m L j : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m) (hj : j ∈ K.erase m) (hjL : j ≠ L)
    {D : WithBot ℕ} (hLow : k2PolyNagaoJRes_Low p K m L hmL j D) (c : Polynomial (ZMod p))
    {z : I → Polynomial (ZMod p)} (hz : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = z)
    (hS : k2PolyNagaoJRes_Sj m L j z) (hd : (z m).degree < D) :
    k2PolyNagaoJRes_Ck p K m L hmL (x j L hjL c) z := by
  have hmj : m ≠ j := (Finset.ne_of_mem_erase hj).symm
  have hjK : j ∈ K := Finset.mem_of_mem_erase hj
  have hωQ := k2PolyNagaoJRes_om_mem_Q (p := p) L hmj hmK hjK
  have hωG := k2PolyNagaoWide_Q_le_G K L hωQ
  have hxG := k2PolyEuclid_x_mem_G (K := K) hjL c (Finset.mem_insert_of_mem hjK)
    (Finset.mem_insert_self L K)
  have hd' : (act (w m j hmj (1 : (Polynomial (ZMod p))ˣ)) z j).degree < D := by
    rw [k2PolyNagaoJRes_om_j hmj z, Polynomial.degree_neg]
    exact hd
  exact k2PolyNagaoJRes_Ck_conj (k2PolyNagaoJRes_xjL_eq hmj hmL hjL c)
    (k2PolyNagaoJRes_Ck_Q hmL hmK hLK hthird hStab hωQ hz)
    (k2PolyNagaoJRes_Ck_xmL hmL hmK hLK hthird hStab hj hLow c (k2PolyNF_orbit_act hωG hz)
      (k2PolyNagaoJRes_Sj_om hmj hS) hd')
    (k2PolyNagaoJRes_Ck_Q hmL hmK hLK hthird hStab hωQ (k2PolyNF_orbit_act hxG hz))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Ck_xjL

/-- The conjugation identity of `k2PolyNagaoJRes_caseB`: `y = A⁻¹ (C y) A` for
`A = x_jm(q)`, `C = x_jL(q)` (`⁅x_jm(q), x_mL(1)⁆ = x_jL(q)`). -/
theorem k2PolyNagaoJRes_y_conj {m L j : I} (hjm : j ≠ m) (hmL : m ≠ L) (hjL : j ≠ L)
    (q : Polynomial (ZMod p)) :
    x m L hmL (1 : Polynomial (ZMod p)) =
      (x j m hjm q)⁻¹ * (x j L hjL q * x m L hmL (1 : Polynomial (ZMod p))) * x j m hjm q := by
  have hc := x_commutator j m L hjm hmL hjL q (1 : Polynomial (ZMod p))
  rw [mul_one] at hc
  rw [← hc, commutatorElement_def]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_y_conj

/-- **One reduction** under `Low D`: the check of `y` at `v` supported on `{m, L, j}` with
`deg (v_j % v_m) < D` and `deg (v_m + v_L) < D`.  (For `v_m = 0`, `v_j % 0 = v_j`.) -/
theorem k2PolyNagaoJRes_caseB {K : Finset I} {m L j : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m) (hj : j ∈ K.erase m) {D : WithBot ℕ}
    (hLow : k2PolyNagaoJRes_Low p K m L hmL j D) {v : I → Polynomial (ZMod p)}
    (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) (hS : k2PolyNagaoJRes_Sj m L j v)
    (h1 : (v j % v m).degree < D) (h2 : (v m + v L).degree < D) :
    k2PolyNagaoJRed_Chk p K m L hmL v := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hjK : j ∈ K := Finset.mem_of_mem_erase hj
  have hjL : j ≠ L := fun e => hLK (by rw [← e]; exact hjK)
  obtain ⟨q, hq⟩ : ∃ q : Polynomial (ZMod p), q = -(v j / v m) := ⟨_, rfl⟩
  have hAQ := k2PolyNagaoJRes_x_mem_Q L hjm q (Finset.mem_insert_of_mem hjK) hmK
  have hyG := k2PolyEuclid_x_mem_G (K := K) hmL (1 : Polynomial (ZMod p))
    (Finset.mem_insert_of_mem hmK) (Finset.mem_insert_self L K)
  have hv1 := k2PolyNF_orbit_act (k2PolyNagaoWide_Q_le_G K L hAQ) hv
  have hS1 := k2PolyNagaoJRes_Sj_x hjm (Or.inr (Or.inr rfl)) q hS
  have e1 : act (x j m hjm q) v j = v j % v m := by
    have hd := EuclideanDomain.div_add_mod (v j) (v m)
    rw [k2PolyNagaoJRes_act_x_self, hq]
    linear_combination -hd
  have e2 : act (x m L hmL (1 : Polynomial (ZMod p))) (act (x j m hjm q) v) m =
      v m + v L := by
    rw [k2PolyNagaoJRes_act_x_self, one_mul, k2PolyNagaoWide_act_x_ne hjm q v hjm.symm,
      k2PolyNagaoWide_act_x_ne hjm q v hjL.symm]
  refine (k2PolyNagaoJRes_Ck_y hmL v).1 (k2PolyNagaoJRes_Ck_conj
    (k2PolyNagaoJRes_y_conj hjm hmL hjL q)
    (k2PolyNagaoJRes_Ck_Q hmL hmK hLK hthird hStab hAQ hv)
    (k2PolyNagaoJRes_Ck_mul ?_ ?_)
    (k2PolyNagaoJRes_Ck_Q hmL hmK hLK hthird hStab hAQ (k2PolyNF_orbit_act hyG hv)))
  · exact k2PolyNagaoJRes_Ck_xjL hmL hmK hLK hthird hStab hj hjL hLow q
      (k2PolyNF_orbit_act hyG hv1)
      (k2PolyNagaoJRes_Sj_x hmL (Or.inl rfl) (1 : Polynomial (ZMod p)) hS1)
      (by rw [e2]; exact h2)
  · exact (k2PolyNagaoJRes_Ck_y hmL _).2 (hLow _ hv1 hS1 (by rw [e1]; exact h1))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_caseB

end GroupApproximation.BooneHigman.Metabelian.ElemFP
