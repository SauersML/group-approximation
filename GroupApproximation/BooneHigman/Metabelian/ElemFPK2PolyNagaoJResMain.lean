import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJResCore
import GroupApproximation.Meta.AxiomGuard

/-!
# The residual root check, part 5: the residual `k2PolyNagaoJRed_ResAt p`, for every prime

Lane `bh-met-94e`.  Notation of `ElemFPK2PolyNagaoJResStep`; fix `j ∈ K \ {m}`.

* `k2PolyNagaoJRes_step`: for `v` supported on `{m, L, j}` with `d = v_j ≠ 0`, `Low (deg d)`
  gives the check at `v`.  Transfer along `x_mj(-(v_m / d) + 1), x_Lj(-(v_L / d) - 1) ∈ Q^m`
  to `v'` with `v'_j = d`, `v'_m = v_m % d + d` (degree `deg d`) and `v'_L = v_L % d - d`.
  Then `deg (d % v'_m) < deg d` and `v'_m + v'_L = v_m % d + v_L % d` has degree `< deg d`,
  so `k2PolyNagaoJRes_caseB` applies with `D = deg d`.
* `k2PolyNagaoJRes_all`: strong induction on `natDeg v_j`; the base is `k2PolyNagaoJRes_zero`.
  So the check of `σ` at `y` holds at EVERY orbit vector supported on `{m, L, j}`.
* **`k2PolyNagaoJRes_resAt`: `k2PolyNagaoJRed_ResAt p` for every prime `p`**, and
  `k2PolyNagaoJRes_statement : k2PolyNagaoJRed_Statement`.
* With the torus interface `k2PolyNagaoTorus_torusIface` (lane 94b):
  `k2PolyNagaoJRes_wide : k2PolyNagaoWide_Statement`,
  `k2PolyNagaoJRes_root : k2PolyNagaoRoot_Statement`, and
  `k2PolyNagaoJRes_K2_bot : K2n N F_p[X] = ⊥` for `N ≥ 5`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act unitVec)

variable {I : Type} [Fintype I] [DecidableEq I]

section Induction

variable {p : ℕ} [Fact p.Prime]

/-- **One Euclidean step**: `Low (deg v_j)` gives the check at `v` (supported on `{m, L, j}`,
`v_j ≠ 0`). -/
theorem k2PolyNagaoJRes_step {K : Finset I} {m L j : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m) (hj : j ∈ K.erase m)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v)
    (hS : k2PolyNagaoJRes_Sj m L j v) (h0 : v j ≠ 0)
    (hLow : k2PolyNagaoJRes_Low p K m L hmL j (v j).degree) :
    k2PolyNagaoJRed_Chk p K m L hmL v := by
  have hjm : j ≠ m := Finset.ne_of_mem_erase hj
  have hjK : j ∈ K := Finset.mem_of_mem_erase hj
  have hjL : j ≠ L := fun e => hLK (by rw [← e]; exact hjK)
  have hmj : m ≠ j := hjm.symm
  have hLj : L ≠ j := hjL.symm
  obtain ⟨q1, hq1⟩ : ∃ q : Polynomial (ZMod p), q = -(v m / v j) + 1 := ⟨_, rfl⟩
  obtain ⟨q2, hq2⟩ : ∃ q : Polynomial (ZMod p), q = -(v L / v j) + -1 := ⟨_, rfl⟩
  have hg1 := k2PolyNagaoJRed_x_mem_Qm hmj q1 (Finset.mem_insert_of_mem hmK) hj
  have hg2 := k2PolyNagaoJRed_x_mem_Qm hLj q2 (Finset.mem_insert_self L K) hj
  have hv1 := k2PolyNF_orbit_act (k2PolyEuclid_x_mem_G (K := K) hmj q1
    (Finset.mem_insert_of_mem hmK) (Finset.mem_insert_of_mem hjK)) hv
  have hv2 := k2PolyNF_orbit_act (k2PolyEuclid_x_mem_G (K := K) hLj q2
    (Finset.mem_insert_self L K) (Finset.mem_insert_of_mem hjK)) hv1
  have hS1 := k2PolyNagaoJRes_Sj_x hmj (Or.inl rfl) q1 hS
  have hS2 := k2PolyNagaoJRes_Sj_x hLj (Or.inr (Or.inl rfl)) q2 hS1
  have ej : act (x L j hLj q2) (act (x m j hmj q1) v) j = v j := by
    rw [k2PolyNagaoWide_act_x_ne hLj q2 _ hjL, k2PolyNagaoWide_act_x_ne hmj q1 v hjm]
  have em : act (x L j hLj q2) (act (x m j hmj q1) v) m = v m % v j + v j := by
    have hd := EuclideanDomain.div_add_mod (v m) (v j)
    rw [k2PolyNagaoWide_act_x_ne hLj q2 _ hmL, k2PolyNagaoJRes_act_x_self, hq1]
    linear_combination -hd
  have eL : act (x L j hLj q2) (act (x m j hmj q1) v) L = v L % v j - v j := by
    have hd := EuclideanDomain.div_add_mod (v L) (v j)
    rw [k2PolyNagaoJRes_act_x_self, k2PolyNagaoWide_act_x_ne hmj q1 v hmL.symm,
      k2PolyNagaoWide_act_x_ne hmj q1 v hjm, hq2]
    linear_combination -hd
  have hdm : (act (x L j hLj q2) (act (x m j hmj q1) v) m).degree = (v j).degree := by
    rw [em]
    exact Polynomial.degree_add_eq_right_of_degree_lt (Polynomial.degree_mod_lt _ h0)
  have hm0 : act (x L j hLj q2) (act (x m j hmj q1) v) m ≠ 0 := fun h =>
    h0 (Polynomial.degree_eq_bot.1 (by rw [← hdm, h, Polynomial.degree_zero]))
  refine k2PolyNagaoJRed_transfer hmL hmK hLK hthird hStab hg1 hv ?_
  refine k2PolyNagaoJRed_transfer hmL hmK hLK hthird hStab hg2 hv1 ?_
  refine k2PolyNagaoJRes_caseB hmL hmK hLK hthird hStab hj hLow hv2 hS2 ?_ ?_
  · rw [ej]
    exact (Polynomial.degree_mod_lt _ hm0).trans_eq hdm
  · rw [em, eL]
    have e : v m % v j + v j + (v L % v j - v j) = v m % v j + v L % v j := by ring
    rw [e]
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      (max_lt (Polynomial.degree_mod_lt _ h0) (Polynomial.degree_mod_lt _ h0))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_step

/-- **The check at every orbit vector supported on `{m, L, j}`** (strong induction on
`natDeg v_j`). -/
theorem k2PolyNagaoJRes_all {K : Finset I} {m L j : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m) (hj : j ∈ K.erase m) (n : ℕ) :
    ∀ v : I → Polynomial (ZMod p), (∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) →
      k2PolyNagaoJRes_Sj m L j v → (v j).natDegree = n → k2PolyNagaoJRed_Chk p K m L hmL v := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv hS hn
    by_cases h0 : v j = 0
    · exact k2PolyNagaoJRes_zero hmL hmK hLK hthird hconst hStab hj hv hS h0
    · refine k2PolyNagaoJRes_step hmL hmK hLK hthird hStab hj hv hS h0 ?_
      intro u hu hSu hd
      by_cases hu0 : u j = 0
      · exact k2PolyNagaoJRes_zero hmL hmK hLK hthird hconst hStab hj hu hSu hu0
      · exact ih _ (by rw [← hn]; exact Polynomial.natDegree_lt_natDegree hu0 hd) u hu hSu rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_all

end Induction

/-- **The lane target**: the residual `k2PolyNagaoJRed_ResAt p`, for every prime `p`. -/
theorem k2PolyNagaoJRes_resAt : ∀ (p : ℕ) [Fact p.Prime], k2PolyNagaoJRed_ResAt p := by
  intro p _ I _ _ K m L hmL hLK hmK _ hthird hconst _ hStab v hv j hj hsupp _ _ _
  exact k2PolyNagaoJRes_all hmL hmK hLK hthird hconst hStab hj _ v hv hsupp rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_resAt

/-- The residual of lane `bh-met-94a`, `k2PolyNagaoJRed_Statement`. -/
theorem k2PolyNagaoJRes_statement : k2PolyNagaoJRed_Statement :=
  k2PolyNagaoJRes_resAt

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_statement

/-- With the torus interface (lane 94b): `k2PolyNagaoWide_Statement`. -/
theorem k2PolyNagaoJRes_wide : k2PolyNagaoWide_Statement :=
  k2PolyNagaoJRed_wide_of_statement k2PolyNagaoJRes_statement k2PolyNagaoTorus_torusIface

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_wide

/-- With the torus interface (lane 94b): `k2PolyNagaoRoot_Statement`. -/
theorem k2PolyNagaoJRes_root : k2PolyNagaoRoot_Statement :=
  k2PolyNagaoJRed_root_of_statement k2PolyNagaoJRes_statement k2PolyNagaoTorus_torusIface

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_root

/-- `K₂(N, F_p[X]) = ⊥` for `N ≥ 5`. -/
theorem k2PolyNagaoJRes_K2_bot {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N) :
    K2n N (Polynomial (ZMod p)) = ⊥ :=
  k2PolyNagaoJRed_K2_bot_of_statement k2PolyNagaoJRes_statement k2PolyNagaoTorus_torusIface
    hp hN

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_K2_bot

end GroupApproximation.BooneHigman.Metabelian.ElemFP
