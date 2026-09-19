import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.RootOrbit
import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WeylCheck
import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WideDefs
import GroupApproximation.Meta.AxiomGuard

/-!
# Field port of the root check, part 2a: the pieces independent of the wide section

k2-poly piece A5.2, back half (lane k2-field-b). This is the field port of the first half of
`ElemFPK2PolyNagaoRootCheck` (bh-met-93v). The check targets are `fnZQ F K L = Z ⊔ Q`, per
k2-field-a's answer on the k2-poly board.

* `fnRoot_Q_mono`, `fnRoot_ZQ_mono`: `Q_{{m}} ≤ Q_K` and `Z ⊔ Q_{{m}} ≤ Z ⊔ Q_K` for `m ∈ K`.
* `fnRoot_rank_one`: `σ₀(y v)⁻¹ y σ₀(v) ∈ Z ⊔ Q_K` for `y = x_mL(1)` and every orbit vector
  `v = v_m e_m + v_L e_L`. It is `fnWeyl_genGood_rankOne` at `K = {m}`, transported by
  `fnRoot_orbit_one`. Over `F_p` this needed the constants hypothesis `hconst`; over `F` the
  target `Z ⊔ Q` absorbs it, so there is none.
* `fnRoot_Q_L`: for `q ∈ Q` and `r` supported on `{m, L}`, `(q r)_L = r_L + d r_m`.
* `fnRoot_m_unit`: if also `q r` is supported on `{m, L}`, then `(q r)_m = c r_m` with `c` a unit.
* `fnRoot_supp_x`: `x_mL(1)` keeps the support.

The shift / sigma_supp / check_supp steps need k2-field-a's `fnWide_core`, `fnWide_rep_spec` and
`fnWide_qsel_spec` (WideSpan/WideEuclid/WideSigma), so they go in part 2b. The `F_p = F_2` case
`rep_m` is not ported: over a field the unit factor is a constant torus element, which RootMain
handles uniformly.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnV fnZ)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul act_one
  act_x_apply unitVec unitVec_apply rootSpan rootSpan_mono exists_split act_eq_self_of_rootSpan
  act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

/-- `Q_{{m}} ≤ Q_K` for `m ∈ K`. -/
theorem fnRoot_Q_mono {K : Finset I} {m L : I} (hmK : m ∈ K) :
    fnQ F ({m} : Finset I) L ≤ fnQ F K L := by
  refine sup_le_sup (fun g hg => ?_) (fun g hg => ?_)
  · exact rootSpan_mono (p := fun i j => i ∈ ({m} : Finset I) ∧ j ∈ ({m} : Finset I))
      (q := fun i j => i ∈ K ∧ j ∈ K) (fun i j _ h => ⟨by rw [Finset.mem_singleton.1 h.1];
        exact hmK, by rw [Finset.mem_singleton.1 h.2]; exact hmK⟩) hg
  · exact rootSpan_mono (p := fun i j => i = L ∧ j ∈ ({m} : Finset I))
      (q := fun i j => i = L ∧ j ∈ K) (fun i j _ h => ⟨h.1, by
        rw [Finset.mem_singleton.1 h.2]; exact hmK⟩) hg

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_Q_mono

/-- `Z ⊔ Q_{{m}} ≤ Z ⊔ Q_K` for `m ∈ K`. -/
theorem fnRoot_ZQ_mono {K : Finset I} {m L : I} (hmK : m ∈ K) :
    fnZQ F ({m} : Finset I) L ≤ fnZQ F K L :=
  sup_le_sup_left (fnRoot_Q_mono hmK) _

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_ZQ_mono

/-- **The rank-one check.** `σ₀(y v)⁻¹ y σ₀(v) ∈ Z ⊔ Q_K` for `y = x_mL(1)` and every orbit
vector `v = v_m e_m + v_L e_L`. -/
theorem fnRoot_rank_one {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) {v : I → Polynomial F}
    (hdec : v = v m • unitVec m + v L • unitVec L)
    (hv : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) :
    (fnSigma_sigma F m L hmL (act (x m L hmL (1 : Polynomial F)) v))⁻¹ *
        x m L hmL (1 : Polynomial F) * fnSigma_sigma F m L hmL v ∈ fnZQ F K L := by
  obtain ⟨n, hmn, hLn⟩ := hthird m L
  have hG := fnWeyl_genGood_rankOne (F := F) (K := ({m} : Finset I)) hmL hmn hLn
    (Finset.mem_singleton_self m) (fun _ hi => Finset.mem_singleton.1 hi)
  exact fnRoot_ZQ_mono hmK (hG.2.1.2 v (fnRoot_orbit_one hmL hdec hv))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_rank_one

/-- For `q ∈ Q` and `r` supported on `{m, L}`: `(q r)_L = r_L + d r_m`. Write `q = s x_Lm(d) v'`
with `s ∈ S_K` fixing the `L`-row and `v'` fixing `r`. -/
theorem fnRoot_Q_L {K : Finset I} {m L : I} (hmL : m ≠ L) (hLK : L ∉ K)
    {q : SteinbergGroup I (Polynomial F)} (hq : q ∈ fnQ F K L)
    {r : I → Polynomial F} (hr : fnWide_Supp m L r) :
    ∃ d : Polynomial F, act q r L = r L + d * r m := by
  have hLe : ∀ j : I, j ∈ K → j ≠ L := fun j hj e => hLK (by rw [← e]; exact hj)
  obtain ⟨s, hs, v, hv, rfl⟩ := fn_SV_decomp hLK hq
  have hsplit : ∀ i j : I, i ≠ j → (i = L ∧ j ∈ K) →
      (i = L ∧ j = m) ∨ (i = L ∧ j ∈ K.erase m) := fun i j _ hij => by
    by_cases hjm : j = m
    · exact Or.inl ⟨hij.1, hjm⟩
    · exact Or.inr ⟨hij.1, Finset.mem_erase.2 ⟨hjm, hij.2⟩⟩
  have hcomm : ∀ (i j : I) (hij : i ≠ j) (a b : Polynomial F),
      (i = L ∧ j ∈ K.erase m) → Commute (x L m hmL.symm b) (x i j hij a) :=
    fun i j hij a b hq => x_commute_of_ne L m i j hmL.symm hij (fun e => hmL (e.trans hq.1))
      (hLe j (Finset.mem_of_mem_erase hq.2)) b a
  obtain ⟨d, v', hv', rfl⟩ := exists_split (p := fun i j => i = L ∧ j ∈ K)
    (q := fun i j => i = L ∧ j ∈ K.erase m) hmL.symm hsplit hcomm hv
  have hv'r : act v' r = r :=
    act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K.erase m)
      (fun _ j hq => hr j (Finset.ne_of_mem_erase hq.2) (hLe j (Finset.mem_of_mem_erase hq.2)))
      hv'
  have hsL : ∀ u : I → Polynomial F, act s u L = u L :=
    act_apply_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (fun i _ hq => hLe i hq.1) hs
  refine ⟨d, ?_⟩
  rw [act_mul, act_mul, hv'r, hsL, act_x_apply, if_pos rfl]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_Q_L

omit [Fintype I] in
/-- A vector supported on `{m, L}` is `r_m e_m + r_L e_L`. -/
theorem fnRoot_decomp {m L : I} (hmL : m ≠ L) {r : I → Polynomial F}
    (hr : fnWide_Supp m L r) : r = r m • unitVec m + r L • unitVec L := by
  funext k
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, unitVec_apply, unitVec_apply, smul_eq_mul,
    smul_eq_mul]
  by_cases hkm : k = m
  · rw [hkm, if_pos rfl, if_neg hmL, mul_one, mul_zero, add_zero]
  · by_cases hkL : k = L
    · rw [hkL, if_neg hmL.symm, if_pos rfl, mul_zero, mul_one, zero_add]
    · rw [if_neg hkm, if_neg hkL, mul_zero, mul_zero, add_zero, hr k hkm hkL]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_decomp

/-- `g u = w ⇒ g⁻¹ w = u`. -/
theorem fnRoot_act_inv {g : SteinbergGroup I (Polynomial F)} {u w : I → Polynomial F}
    (h : act g u = w) : act g⁻¹ w = u := by
  rw [← h, ← act_mul, inv_mul_cancel, act_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_act_inv

/-- **The torus factor.** For `q ∈ Q` and `r`, `q r` both supported on `{m, L}`,
`(q r)_m = c r_m` with `c` a unit. -/
theorem fnRoot_m_unit {K : Finset I} {m L : I} (hmL : m ≠ L) (hLK : L ∉ K)
    {q : SteinbergGroup I (Polynomial F)} (hq : q ∈ fnQ F K L)
    {r : I → Polynomial F} (hr : fnWide_Supp m L r) (hs : fnWide_Supp m L (act q r)) :
    ∃ c : Polynomial F, IsUnit c ∧ act q r m = c * r m := by
  have hLe : ∀ j : I, j ∈ K → j ≠ L := fun j hj e => hLK (by rw [← e]; exact hj)
  obtain ⟨s, hs0, v, hv, rfl⟩ := fn_SV_decomp hLK hq
  obtain ⟨r', hr'⟩ : ∃ r' : I → Polynomial F, act v r = r' := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : I → Polynomial F, act s (unitVec m) = t := ⟨_, rfl⟩
  have hr'k : ∀ k : I, k ≠ L → r' k = r k := fun k hk => by
    rw [← hr']
    exact act_apply_of_rootSpan (p := fun i j => i = L ∧ j ∈ K)
      (fun i _ h e => hk (e.symm.trans h.1)) hv r
  have hr'S : fnWide_Supp m L r' := by
    intro k hkm hkL
    rw [hr'k k hkL]
    exact hr k hkm hkL
  have hsE : act s (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K)
      (fun _ j hq => by rw [unitVec_apply, if_neg (hLe j hq.2)]) hs0
  have hsk : ∀ k : I, k ∉ K → t k = unitVec m k := fun k hk => by
    rw [← ht]
    exact act_apply_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K)
      (fun i _ h e => hk (by rw [← e]; exact h.1)) hs0 (unitVec m)
  have hdec : act s r' = r m • t + r' L • unitVec L := by
    rw [congrArg (act s) (fnRoot_decomp hmL hr'S), fnRoot_act_lin, hsE, ht, hr'k m hmL]
  have hcoord : ∀ k : I,
      act (s * v) r k = r m * t k + r' L * (if k = L then 1 else 0) := by
    intro k
    rw [act_mul, hr', hdec, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, unitVec_apply]
  have hm0 : act (s * v) r m = t m * r m := by
    rw [hcoord, if_neg hmL]
    ring
  by_cases hrm : r m = 0
  · exact ⟨1, isUnit_one, by rw [hm0, hrm, mul_zero, mul_zero]⟩
  refine ⟨t m, ?_, hm0⟩
  have htz : ∀ k : I, k ≠ m → t k = 0 := by
    intro k hkm
    by_cases hkK : k ∈ K
    · have h := hs k hkm (hLe k hkK)
      rw [hcoord, if_neg (hLe k hkK), mul_zero, add_zero] at h
      exact (mul_eq_zero.1 h).resolve_left hrm
    · rw [hsk k hkK, unitVec_apply, if_neg hkm]
  have htm : t = t m • unitVec m := funext fun k => by
    rw [Pi.smul_apply, unitVec_apply, smul_eq_mul]
    by_cases hkm : k = m
    · rw [hkm, if_pos rfl, mul_one]
    · rw [if_neg hkm, mul_zero, htz k hkm]
  have hinv := fnRoot_act_inv ht
  rw [htm] at hinv
  have hsm : act s⁻¹ (t m • unitVec m) = t m • act s⁻¹ (unitVec m) := by
    simp only [act, Matrix.mulVec_smul]
  rw [hsm] at hinv
  have h := congrFun hinv m
  rw [Pi.smul_apply, smul_eq_mul, unitVec_apply, if_pos rfl] at h
  exact IsUnit.of_mul_eq_one _ h

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_m_unit

/-- `x_mL(1)` keeps the support `{m, L}`. -/
theorem fnRoot_supp_x {m L : I} (hmL : m ≠ L) {v : I → Polynomial F}
    (hS : fnWide_Supp m L v) :
    fnWide_Supp m L (act (x m L hmL (1 : Polynomial F)) v) := by
  intro k hkm hkL
  rw [act_x_apply, if_neg hkm, add_zero]
  exact hS k hkm hkL

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_supp_x

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
