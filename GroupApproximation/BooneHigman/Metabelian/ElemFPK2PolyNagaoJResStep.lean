import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJResWeyl
import GroupApproximation.Meta.AxiomGuard

/-!
# The residual root check, part 3: support, the induction hypothesis, and `W`

Lane `bh-met-94e`.  Notation of `ElemFPK2PolyNagaoJResCocycle`; fix `j ∈ K \ {m}`.

* `k2PolyNagaoJRes_Sj m L j v`: `v` is supported on `{m, L, j}`.
* `k2PolyNagaoJRes_Low p K m L hmL j D`: the check of `σ` at `y` holds at every orbit vector
  supported on `{m, L, j}` whose `j`-coordinate has degree `< D` (the induction hypothesis).
* `k2PolyNagaoJRes_zero`: the check at `v` supported on `{m, L, j}` with `v_j = 0`
  (the torus check `k2PolyNagaoTorus_check`, third index `j`).
* `k2PolyNagaoJRes_Ck_W`: under `Low D`, the check of `W = w_mL(1) = y x_Lm(-1) y` at every
  supported `u` with `deg u_j < D`.  None of the three factors moves `u_j`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act unitVec
  x_mem_rootSpan)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- `v` is supported on `{m, L, j}`. -/
def k2PolyNagaoJRes_Sj {R : Type} [Zero R] (m L j : I) (v : I → R) : Prop :=
  ∀ k, k ≠ m → k ≠ L → k ≠ j → v k = 0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Sj

/-- **The induction hypothesis**: the check of `σ` at `y` at every orbit vector supported on
`{m, L, j}` whose `j`-coordinate has degree `< D`. -/
def k2PolyNagaoJRes_Low (p : ℕ) [Fact p.Prime] (K : Finset I) (m L : I) (hmL : m ≠ L) (j : I)
    (D : WithBot ℕ) : Prop :=
  ∀ u : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = u) →
    k2PolyNagaoJRes_Sj m L j u → (u j).degree < D → k2PolyNagaoJRed_Chk p K m L hmL u

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Low

variable {p : ℕ} [Fact p.Prime]

/-- A root `x_ik(c)` with `i ∈ {m, L, j}` keeps the support `{m, L, j}`. -/
theorem k2PolyNagaoJRes_Sj_x {m L j i k : I} (hik : i ≠ k) (hi : i = m ∨ i = L ∨ i = j)
    (c : Polynomial (ZMod p)) {v : I → Polynomial (ZMod p)}
    (hS : k2PolyNagaoJRes_Sj m L j v) : k2PolyNagaoJRes_Sj m L j (act (x i k hik c) v) := by
  intro l hlm hlL hlj
  have hli : l ≠ i := by
    rcases hi with h | h | h
    · rw [h]
      exact hlm
    · rw [h]
      exact hlL
    · rw [h]
      exact hlj
  rw [k2PolyNagaoWide_act_x_ne hik c v hli]
  exact hS l hlm hlL hlj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Sj_x

/-- `ω = w_mj(1)` keeps the support `{m, L, j}`. -/
theorem k2PolyNagaoJRes_Sj_om {m L j : I} (hmj : m ≠ j) {v : I → Polynomial (ZMod p)}
    (hS : k2PolyNagaoJRes_Sj m L j v) :
    k2PolyNagaoJRes_Sj m L j (act (w m j hmj (1 : (Polynomial (ZMod p))ˣ)) v) := by
  intro l hlm hlL hlj
  rw [k2PolyNagaoJRes_om_other hmj v hlm hlj]
  exact hS l hlm hlL hlj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Sj_om

/-- A root `x_ik(c)` with `i ∈ K ∪ {L}`, `k ∈ K` lies in `Q`. -/
theorem k2PolyNagaoJRes_x_mem_Q {K : Finset I} {i k : I} (L : I) (hik : i ≠ k)
    (c : Polynomial (ZMod p)) (hi : i ∈ insert L K) (hk : k ∈ K) :
    x i k hik c ∈ k2PolyNF_Q p K L :=
  k2PolyNagaoWide_Qr_le_Q K L
    (x_mem_rootSpan (p := fun a b => a ∈ insert L K ∧ b ∈ K) hik c ⟨hi, hk⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_x_mem_Q

/-- **The zero case**: `v` supported on `{m, L, j}` with `v_j = 0` is supported on `{m, L}`,
where the torus check applies (third index `j ∈ K`). -/
theorem k2PolyNagaoJRes_zero {K : Finset I} {m L j : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m) (hj : j ∈ K.erase m)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v)
    (hS : k2PolyNagaoJRes_Sj m L j v) (h0 : v j = 0) : k2PolyNagaoJRed_Chk p K m L hmL v := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hjK : j ∈ K := Finset.mem_of_mem_erase hj
  have hLj : L ≠ j := fun e => hLK (by rw [e]; exact hjK)
  refine k2PolyNagaoTorus_check hmL hjm.symm hLj hmK hjK hLK hthird hconst hStab hv ?_
  intro k hkm hkL
  by_cases hkj : k = j
  · rw [hkj]
    exact h0
  · exact hS k hkm hkL hkj

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_zero

/-- **The check of `W = w_mL(1)`** under `Low D`, at `u` supported on `{m, L, j}` with
`deg u_j < D`: `W = y x_Lm(-1) y`, the outer factors are checked by `Low D` (neither moves
`u_j`), the middle one lies in `V ≤ Q`. -/
theorem k2PolyNagaoJRes_Ck_W {K : Finset I} {m L j : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m) (hj : j ∈ K.erase m) {D : WithBot ℕ}
    (hLow : k2PolyNagaoJRes_Low p K m L hmL j D) {u : I → Polynomial (ZMod p)}
    (hu : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = u) (hS : k2PolyNagaoJRes_Sj m L j u)
    (hd : (u j).degree < D) :
    k2PolyNagaoJRes_Ck p K m L hmL (w m L hmL (1 : (Polynomial (ZMod p))ˣ)) u := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hjL : j ≠ L := fun e => hLK (by rw [← e]; exact Finset.mem_of_mem_erase hj)
  have hyG := k2PolyEuclid_x_mem_G (K := K) hmL (1 : Polynomial (ZMod p))
    (Finset.mem_insert_of_mem hmK) (Finset.mem_insert_self L K)
  have hXG := k2PolyEuclid_x_mem_G (K := K) hmL.symm (-1 : Polynomial (ZMod p))
    (Finset.mem_insert_self L K) (Finset.mem_insert_of_mem hmK)
  have hXQ := k2PolyNagaoJRes_x_mem_Q L hmL.symm (-1 : Polynomial (ZMod p))
    (Finset.mem_insert_self L K) hmK
  have hu1 := k2PolyNF_orbit_act hyG hu
  have hu2 := k2PolyNF_orbit_act hXG hu1
  have hS1 := k2PolyNagaoJRes_Sj_x hmL (Or.inl rfl) (1 : Polynomial (ZMod p)) hS
  have hS2 := k2PolyNagaoJRes_Sj_x hmL.symm (Or.inr (Or.inl rfl)) (-1 : Polynomial (ZMod p)) hS1
  have hj2 : act (x L m hmL.symm (-1 : Polynomial (ZMod p)))
      (act (x m L hmL (1 : Polynomial (ZMod p))) u) j = u j := by
    rw [k2PolyNagaoWide_act_x_ne hmL.symm _ _ hjL, k2PolyNagaoWide_act_x_ne hmL _ _ hjm]
  rw [k2PolyNagaoJRes_om_eq hmL]
  refine k2PolyNagaoJRes_Ck_mul ?_ ((k2PolyNagaoJRes_Ck_y hmL u).2 (hLow u hu hS hd))
  refine k2PolyNagaoJRes_Ck_mul ?_ (k2PolyNagaoJRes_Ck_Q hmL hmK hLK hthird hStab hXQ hu1)
  exact (k2PolyNagaoJRes_Ck_y hmL _).2 (hLow _ hu2 hS2 (by rw [hj2]; exact hd))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_Ck_W

end GroupApproximation.BooneHigman.Metabelian.ElemFP
