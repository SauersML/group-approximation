import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWideSpan
import GroupApproximation.Meta.AxiomGuard

/-!
# The wide Nagao step, part 2: the stabiliser of a two-coordinate vector

Lane `bh-met-93l`.  Notation of `ElemFPK2PolyNagaoWideSpan`; `J = K \ {m}`, `σ₀ = pair`.

* `k2PolyNagaoWide_Stab p K L`: `Stab_G(e_L) = Q` (the conclusion of `k2PolyNF_StabStatement`,
  at one `K`, `L`).
* `k2PolyNagaoWide_Supp m L r`: `r` is supported on `{m, L}`.
* `k2PolyNagaoWide_mem_Qm`: if `Stab(J, m)` holds, `t ∈ Q` fixes such an `r` and `r m ≠ 0`,
  then `t ∈ Q^m`.  Write `t = s v` (`s ∈ S_K`, `v ∈ V`), split `v = x_Lm(d) v'`; the
  `L`-coordinate gives `d r_m = 0`, so `d = 0`; then `s r = r`, and linearity with `s e_L = e_L`
  gives `s e_m = e_m`, so `s ∈ Q_{J,m} ≤ Q^m` by `Stab(J, m)`.
* `k2PolyNagaoWide_core`: `σ₀(r)⁻¹ t σ₀(r) ∈ Q` for such `t`, `r`: for `r m ≠ 0` because
  `σ₀(r) ∈ G_{mL}` normalises `Q^m`; for `r m = 0`, `σ₀(r) = τ(r_L)` is `1` or a constant torus
  element, which normalises `Q`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act act_mul
  act_one act_x_apply unitVec unitVec_apply rootSpan_mono exists_split act_eq_self_of_rootSpan
  act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I]

section Defs

variable (p : ℕ) [Fact p.Prime]

/-- `Stab_G(e_L) = Q` at one `K`, `L`. -/
def k2PolyNagaoWide_Stab (K : Finset I) (L : I) : Prop :=
  ∀ g ∈ k2PolyDeg_G p K L, act g (unitVec L) = unitVec L → g ∈ k2PolyNF_Q p K L

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Stab

end Defs

/-- `r` is supported on `{m, L}`. -/
def k2PolyNagaoWide_Supp {R : Type} [Zero R] (m L : I) (r : I → R) : Prop :=
  ∀ i, i ≠ m → i ≠ L → r i = 0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_Supp

variable {p : ℕ} [Fact p.Prime]

/-- The action is linear. -/
theorem k2PolyNagaoWide_act_lin (g : SteinbergGroup I (Polynomial (ZMod p)))
    (a b : Polynomial (ZMod p)) (u v : I → Polynomial (ZMod p)) :
    act g (a • u + b • v) = a • act g u + b • act g v := by
  simp only [act, Matrix.mulVec_add, Matrix.mulVec_smul]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_act_lin

/-- `Stab(J, m)` puts every `s ∈ S_K` fixing `e_m` into `Q^m`. -/
theorem k2PolyNagaoWide_S_mem_Qm {K : Finset I} {m L : I} (hmK : m ∈ K)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m) {s : SteinbergGroup I (Polynomial (ZMod p))}
    (hs : s ∈ k2PolyDeg_S p K) (hfix : act s (unitVec m) = unitVec m) :
    s ∈ k2PolyNagaoWide_Qm p K m L := by
  have hKe : insert m (K.erase m) = K := Finset.insert_erase hmK
  have hsG : s ∈ k2PolyDeg_G p (K.erase m) m :=
    rootSpan_mono (p := fun i j => i ∈ K ∧ j ∈ K)
      (q := fun i j => i ∈ insert m (K.erase m) ∧ j ∈ insert m (K.erase m))
      (fun _ _ _ hij => ⟨by rw [hKe]; exact hij.1, by rw [hKe]; exact hij.2⟩) hs
  have hsQ := k2PolyNagaoWide_Q_le_Qr (K.erase m) m (hStab s hsG hfix)
  exact rootSpan_mono (p := fun i j => i ∈ insert m (K.erase m) ∧ j ∈ K.erase m)
    (q := fun i j => i ∈ insert L K ∧ j ∈ K.erase m)
    (fun _ _ _ hij => ⟨Finset.mem_insert_of_mem (by rw [← hKe]; exact hij.1), hij.2⟩) hsQ

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_S_mem_Qm

/-- A vector supported on `{m, L}` is `r_m e_m + r_L e_L`. -/
theorem k2PolyNagaoWide_decomp {m L : I} (hmL : m ≠ L) {r : I → Polynomial (ZMod p)}
    (hr : k2PolyNagaoWide_Supp m L r) : r = r m • unitVec m + r L • unitVec L := by
  funext k
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, unitVec_apply, unitVec_apply, smul_eq_mul,
    smul_eq_mul]
  by_cases hkm : k = m
  · rw [hkm, if_pos rfl, if_neg hmL, mul_one, mul_zero, add_zero]
  · by_cases hkL : k = L
    · rw [hkL, if_neg hmL.symm, if_pos rfl, mul_zero, mul_one, zero_add]
    · rw [if_neg hkm, if_neg hkL, mul_zero, mul_zero, add_zero, hr k hkm hkL]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_decomp

/-- **Key step.**  With `Stab(J, m)`, an element `t ∈ Q` fixing `r` (supported on `{m, L}`,
`r m ≠ 0`) lies in `Q^m`. -/
theorem k2PolyNagaoWide_mem_Qm {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {r : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L r) (hrm : r m ≠ 0)
    {t : SteinbergGroup I (Polynomial (ZMod p))} (ht : t ∈ k2PolyNF_Q p K L)
    (htr : act t r = r) : t ∈ k2PolyNagaoWide_Qm p K m L := by
  have hLe : ∀ j : I, j ∈ K → j ≠ L := fun j hj e => hLK (by rw [← e]; exact hj)
  obtain ⟨s, hs, v, hv, rfl⟩ := k2PolyDeg_SV_decomp hLK ht
  have hsplit : ∀ i j : I, i ≠ j → (i = L ∧ j ∈ K) →
      (i = L ∧ j = m) ∨ (i = L ∧ j ∈ K.erase m) := fun i j _ hij => by
    by_cases hjm : j = m
    · exact Or.inl ⟨hij.1, hjm⟩
    · exact Or.inr ⟨hij.1, Finset.mem_erase.2 ⟨hjm, hij.2⟩⟩
  have hcomm : ∀ (i j : I) (hij : i ≠ j) (a b : Polynomial (ZMod p)),
      (i = L ∧ j ∈ K.erase m) → Commute (x L m hmL.symm b) (x i j hij a) :=
    fun i j hij a b hq => x_commute_of_ne L m i j hmL.symm hij (fun e => hmL (e.trans hq.1))
      (hLe j (Finset.mem_of_mem_erase hq.2)) b a
  obtain ⟨d, v', hv', rfl⟩ := exists_split (p := fun i j => i = L ∧ j ∈ K)
    (q := fun i j => i = L ∧ j ∈ K.erase m) hmL.symm hsplit hcomm hv
  have hv'r : act v' r = r :=
    act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K.erase m)
      (fun _ j hq => hr j (Finset.ne_of_mem_erase hq.2) (hLe j (Finset.mem_of_mem_erase hq.2)))
      hv'
  have hsL : ∀ u : I → Polynomial (ZMod p), act s u L = u L :=
    act_apply_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (fun i _ hq => hLe i hq.1) hs
  rw [act_mul, act_mul, hv'r] at htr
  have hL := congrFun htr L
  rw [hsL, act_x_apply, if_pos rfl] at hL
  have hd0 : d * r m = 0 := by linear_combination hL
  have hd : d = 0 := (mul_eq_zero.1 hd0).resolve_right hrm
  subst hd
  rw [x_zero, act_one] at htr
  have hsE : act s (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K)
      (fun _ j hq => by rw [unitVec_apply, if_neg (hLe j hq.2)]) hs
  have h2 : act s (r m • unitVec m + r L • unitVec L) = r m • unitVec m + r L • unitVec L := by
    rw [← k2PolyNagaoWide_decomp hmL hr]
    exact htr
  rw [k2PolyNagaoWide_act_lin, hsE] at h2
  have h3 := add_right_cancel h2
  have hsm : act s (unitVec m) = unitVec m := funext fun k => by
    have h4 := congrFun h3 k
    simp only [Pi.smul_apply, smul_eq_mul] at h4
    exact mul_left_cancel₀ hrm h4
  rw [x_zero, one_mul]
  exact Subgroup.mul_mem _ (k2PolyNagaoWide_S_mem_Qm hmK hStab hs hsm)
    (rootSpan_mono (p := fun i j => i = L ∧ j ∈ K.erase m)
      (q := fun i j => i ∈ insert L K ∧ j ∈ K.erase m)
      (fun _ _ _ hij => ⟨Finset.mem_insert.2 (Or.inl hij.1), hij.2⟩) hv')

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_mem_Qm

/-- **The core check.**  `σ₀(r)⁻¹ t σ₀(r) ∈ Q` for `t ∈ Q` fixing `r` (supported on
`{m, L}`), given `Stab(J, m)`. -/
theorem k2PolyNagaoWide_core {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {r : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L r)
    {t : SteinbergGroup I (Polynomial (ZMod p))} (ht : t ∈ k2PolyNF_Q p K L)
    (htr : act t r = r) :
    (k2PolyNagaoSigma_sigma p m L hmL r)⁻¹ * t * k2PolyNagaoSigma_sigma p m L hmL r ∈
      k2PolyNF_Q p K L := by
  by_cases hrm : r m = 0
  · rw [k2PolyNagaoSigma_sigma, hrm, k2PolyNagaoSigma_pair_zero]
    by_cases hu : IsUnit (r L)
    · obtain ⟨n, hmn, hLn⟩ := hthird m L
      obtain ⟨β, hβ⟩ := k2PolyNagaoWeyl_exists_C_of_isUnit hu
      rw [hβ, k2PolyNagaoWeyl_tau_C hmL hmn hLn, inv_inv]
      exact k2PolyNagaoWide_Qr_le_Q K L (k2PolyDeg_torus_conj_rootSpan m L n hmL hmn hLn
        (fun i j => i ∈ insert L K ∧ j ∈ K) β (k2PolyNagaoWide_Q_le_Qr K L ht))
    · rw [k2PolyNagaoSigma_tau, if_neg (fun e => hu (by rw [e]; exact isUnit_one)),
        dif_neg hu, inv_one, one_mul, mul_one]
      exact ht
  · have h := k2PolyNagaoWide_Gml_conj_Qm hmK hLK
      (Subgroup.inv_mem _ (k2PolyNagaoWide_sigma0_mem hmL r))
      (k2PolyNagaoWide_mem_Qm hmL hmK hLK hStab hr hrm ht htr)
    rw [inv_inv] at h
    exact k2PolyNagaoWide_Qm_le_Q K m L h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoWide_core

end GroupApproximation.BooneHigman.Metabelian.ElemFP
