import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WideDefs
import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WeylCheck
import GroupApproximation.BooneHigmanLinear.K2Poly.FieldZCentral
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: root spans around `Q`, and the core check of the wide step

k2-poly piece A5.2 (lane k2-field-a). The field port of lane 93l's `ElemFPK2PolyNagaoWideSpan`
and `…WideStab`. Notation of `FieldNF.WideDefs`.

* `fnWide_Q_le_Qr`, `fnWide_Qr_le_Q`, `fnWide_Qm_le_Q`; `G_{mL}` contains every Euclidean word
  (`fnWide_pair_mem`) and normalizes `Q^m` (`fnWide_Gml_conj_Qm`).
* `fnWide_mem_ZQm`: with `Stab(J, m)`, an element `t ∈ Q` fixing `r` (supported on `{m, L}`,
  `r m ≠ 0`) lies in `Z ⊔ Q^m`. Over `F_p` it lies in `Q^m`. Over a field, `Stab(J, m)` only
  gives `Z ⊔ Q_{J,m}`.
* `fnWide_core`: `σ₀(r)⁻¹ t σ₀(r) ∈ Z ⊔ Q` for such `t`, `r`. The case `r m ≠ 0` writes
  `t = z u` (`z ∈ Z`, `u ∈ Q^m`) and uses that `Z` is central (A5.1, `K2Poly.fnZ_central`).
  The case `r m = 0` is a torus conjugation, exact as over `F_p`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnV fnZ fieldTorus fieldTorus_conj_rootSpan
  fnZ_central)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h x_congr conj_x_left
  conj_of_commute)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  x_mem_rootSpan rootSpan_induction rootSpan_mono rootSpan_normalizes act act_mul act_one
  act_x_apply unitVec unitVec_apply exists_split act_eq_self_of_rootSpan act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

/-- `Q ≤ Q_r`. -/
theorem fnWide_Q_le_Qr (K : Finset I) (L : I) : fnQ F K L ≤ fnWide_Qr F K L := by
  show fnS F K ⊔ fnV F K L ≤ fnWide_Qr F K L
  refine sup_le (fun _ hg => ?_) (fun _ hg => ?_)
  · exact rootSpan_mono (p := fun i j => i ∈ K ∧ j ∈ K)
      (q := fun i j => i ∈ insert L K ∧ j ∈ K)
      (fun _ _ _ hij => ⟨Finset.mem_insert_of_mem hij.1, hij.2⟩) hg
  · exact rootSpan_mono (p := fun i j => i = L ∧ j ∈ K)
      (q := fun i j => i ∈ insert L K ∧ j ∈ K)
      (fun _ _ _ hij => ⟨Finset.mem_insert.2 (Or.inl hij.1), hij.2⟩) hg

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Q_le_Qr

/-- `Q_r ≤ Q`. -/
theorem fnWide_Qr_le_Q (K : Finset I) (L : I) : fnWide_Qr F K L ≤ fnQ F K L := by
  intro _ hg
  refine rootSpan_induction (p := fun i j => i ∈ insert L K ∧ j ∈ K)
    (Q := fun g => g ∈ fnQ F K L) ?_ (Subgroup.one_mem _)
    (fun _ _ _ _ h1 h2 => Subgroup.mul_mem _ h1 h2) hg
  intro i j hij a hq
  have hq' : i ∈ insert L K ∧ j ∈ K := hq
  show x i j hij a ∈ fnS F K ⊔ fnV F K L
  rcases Finset.mem_insert.1 hq'.1 with hiL | hiK
  · exact Subgroup.mem_sup_right
      (x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K) hij a ⟨hiL, hq'.2⟩)
  · exact Subgroup.mem_sup_left
      (x_mem_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) hij a ⟨hiK, hq'.2⟩)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Qr_le_Q

/-- `Q^m ≤ Q`. -/
theorem fnWide_Qm_le_Q (K : Finset I) (m L : I) : fnWide_Qm F K m L ≤ fnQ F K L := fun _ hg =>
  fnWide_Qr_le_Q K L <| rootSpan_mono (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m)
    (q := fun i j => i ∈ insert L K ∧ j ∈ K)
    (fun _ _ _ hij => ⟨hij.1, Finset.mem_of_mem_erase hij.2⟩) hg

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Qm_le_Q

variable {m L : I}

/-- The roots `x_ij(f)`, `i, j ∈ {m, L}`, lie in `G_{mL}`. -/
theorem fnWide_x_mem_Gml {i j : I} (hij : i ≠ j) (hi : i = m ∨ i = L) (hj : j = m ∨ j = L)
    (a : Polynomial F) : x i j hij a ∈ fnWide_Gml F m L :=
  x_mem_rootSpan (p := fun i j => (i = m ∨ i = L) ∧ (j = m ∨ j = L)) hij a ⟨hi, hj⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_x_mem_Gml

/-- `w_mL(u) ∈ G_{mL}`. -/
theorem fnWide_w_mem (hmL : m ≠ L) (u : (Polynomial F)ˣ) :
    w m L hmL u ∈ fnWide_Gml F m L := by
  rw [w]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (fnWide_x_mem_Gml hmL (Or.inl rfl) (Or.inr rfl) _)
      (fnWide_x_mem_Gml hmL.symm (Or.inr rfl) (Or.inl rfl) _))
    (fnWide_x_mem_Gml hmL (Or.inl rfl) (Or.inr rfl) _)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_w_mem

/-- `h_mL(u) ∈ G_{mL}`. -/
theorem fnWide_h_mem (hmL : m ≠ L) (u : (Polynomial F)ˣ) :
    h m L hmL u ∈ fnWide_Gml F m L := by
  show w m L hmL u * w m L hmL (-1) ∈ fnWide_Gml F m L
  exact Subgroup.mul_mem _ (fnWide_w_mem hmL u) (fnWide_w_mem hmL (-1))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_h_mem

/-- `τ(b) ∈ G_{mL}`. -/
theorem fnWide_tau_mem (hmL : m ≠ L) (b : Polynomial F) :
    fnSigma_tau F m L hmL b ∈ fnWide_Gml F m L := by
  unfold fnSigma_tau
  split_ifs
  · exact Subgroup.one_mem _
  · exact Subgroup.inv_mem _ (fnWide_h_mem hmL _)
  · exact Subgroup.one_mem _

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_tau_mem

/-- Every Euclidean word `pair a b` lies in `G_{mL}`. -/
theorem fnWide_pair_mem (hmL : m ≠ L) (a : Polynomial F) :
    ∀ b, fnSigma_pair F m L hmL a b ∈ fnWide_Gml F m L := by
  induction a using (Polynomial.degree_lt_wf (R := F)).induction with
  | _ a ih =>
    intro b
    by_cases ha : a = 0
    · rw [ha, fnSigma_pair_zero]
      exact fnWide_tau_mem hmL b
    · rw [fnSigma_pair_of_ne m L hmL ha]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (fnWide_x_mem_Gml hmL.symm (Or.inr rfl) (Or.inl rfl) _)
          (fnWide_w_mem hmL _))
        (ih _ (Polynomial.degree_mod_lt b ha) _)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_pair_mem

/-- `σ₀(v) = pair (v m) (v L) ∈ G_{mL}`. -/
theorem fnWide_sigma0_mem (hmL : m ≠ L) (v : I → Polynomial F) :
    fnSigma_sigma F m L hmL v ∈ fnWide_Gml F m L :=
  fnWide_pair_mem hmL (v m) (v L)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_sigma0_mem

/-- `G_{mL}` normalizes `Q^m`. -/
theorem fnWide_Gml_conj_Qm {K : Finset I} (hmK : m ∈ K) (hLK : L ∉ K)
    {s : SteinbergGroup I (Polynomial F)} (hs : s ∈ fnWide_Gml F m L)
    {u : SteinbergGroup I (Polynomial F)} (hu : u ∈ fnWide_Qm F K m L) :
    s * u * s⁻¹ ∈ fnWide_Qm F K m L := by
  refine rootSpan_normalizes (p := fun i j => (i = m ∨ i = L) ∧ (j = m ∨ j = L))
    (q := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) ?_ hs hu
  intro a b hab c hp k l hkl d hq
  have hp' : (a = m ∨ a = L) ∧ (b = m ∨ b = L) := hp
  have hq' : k ∈ insert L K ∧ l ∈ K.erase m := hq
  have hlm : l ≠ m := Finset.ne_of_mem_erase hq'.2
  have hlL : l ≠ L := fun e => hLK (by rw [← e]; exact Finset.mem_of_mem_erase hq'.2)
  have hal : a ≠ l := by
    rcases hp'.1 with e | e
    · exact fun e' => hlm (e'.symm.trans e)
    · exact fun e' => hlL (e'.symm.trans e)
  have haK : a ∈ insert L K := by
    rcases hp'.1 with e | e
    · exact Finset.mem_insert_of_mem (by rw [e]; exact hmK)
    · exact Finset.mem_insert.2 (Or.inl e)
  by_cases hbk : b = k
  · have hbl : b ≠ l := fun e => hkl (hbk.symm.trans e)
    have hbK : b ∈ insert L K := by rw [hbk]; exact hq'.1
    rw [x_congr hkl hbl hbk.symm rfl (rfl : d = d), conj_x_left a b l hab hbl hal c d]
    exact Subgroup.mul_mem _
      (x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) hal _ ⟨haK, hq'.2⟩)
      (x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) hbl _ ⟨hbK, hq'.2⟩)
  · rw [conj_of_commute (x_commute_of_ne a b k l hab hkl hbk (Ne.symm hal) c d)]
    exact x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ K.erase m) hkl d hq'

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Gml_conj_Qm

/-- The action is linear. -/
theorem fnWide_act_lin (g : SteinbergGroup I (Polynomial F)) (a b : Polynomial F)
    (u v : I → Polynomial F) : act g (a • u + b • v) = a • act g u + b • act g v := by
  simp only [act, Matrix.mulVec_add, Matrix.mulVec_smul]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_act_lin

/-- With `Z` central, every element of `Z ⊔ H` is `z u` with `z ∈ Z`, `u ∈ H`. -/
theorem fnWide_Zsup_decomp (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    {H : Subgroup (SteinbergGroup I (Polynomial F))} {g : SteinbergGroup I (Polynomial F)}
    (hg : g ∈ fnZ F ⊔ H) : ∃ z ∈ fnZ F, ∃ u ∈ H, z * u = g := by
  have hg' : g ∈ (fnZ F : Set (SteinbergGroup I (Polynomial F))) *
      (H : Set (SteinbergGroup I (Polynomial F))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (fn_Z_le_normalizer (fun _ hz g => fnZ_central hthird hz g) H)]
    exact hg
  exact Set.mem_mul.mp hg'

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_Zsup_decomp

/-- `Stab(J, m)` puts every `s ∈ S_K` fixing `e_m` into `Z ⊔ Q^m`. -/
theorem fnWide_S_mem_ZQm {K : Finset I} (hmK : m ∈ K) (hStab : fnWide_Stab F (K.erase m) m)
    {s : SteinbergGroup I (Polynomial F)} (hs : s ∈ fnS F K)
    (hfix : act s (unitVec m) = unitVec m) : s ∈ fnZ F ⊔ fnWide_Qm F K m L := by
  have hKe : insert m (K.erase m) = K := Finset.insert_erase hmK
  have hsG : s ∈ fnS F (insert m (K.erase m)) :=
    rootSpan_mono (p := fun i j => i ∈ K ∧ j ∈ K)
      (q := fun i j => i ∈ insert m (K.erase m) ∧ j ∈ insert m (K.erase m))
      (fun _ _ _ hij => ⟨by rw [hKe]; exact hij.1, by rw [hKe]; exact hij.2⟩) hs
  have hsZQ : s ∈ fnZQ F (K.erase m) m := hStab s hsG hfix
  have hle : fnQ F (K.erase m) m ≤ fnWide_Qm F K m L := fun _ hq =>
    rootSpan_mono (p := fun i j => i ∈ insert m (K.erase m) ∧ j ∈ K.erase m)
      (q := fun i j => i ∈ insert L K ∧ j ∈ K.erase m)
      (fun _ _ _ hij => ⟨Finset.mem_insert_of_mem (by rw [← hKe]; exact hij.1), hij.2⟩)
      (fnWide_Q_le_Qr (K.erase m) m hq)
  exact (sup_le_sup_left hle (fnZ F)) hsZQ

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_S_mem_ZQm

omit [Fintype I] in
/-- A vector supported on `{m, L}` is `r_m e_m + r_L e_L`. -/
theorem fnWide_decomp (hmL : m ≠ L) {r : I → Polynomial F} (hr : fnWide_Supp m L r) :
    r = r m • unitVec m + r L • unitVec L := by
  funext k
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, unitVec_apply, unitVec_apply, smul_eq_mul,
    smul_eq_mul]
  by_cases hkm : k = m
  · rw [hkm, if_pos rfl, if_neg hmL, mul_one, mul_zero, add_zero]
  · by_cases hkL : k = L
    · rw [hkL, if_neg hmL.symm, if_pos rfl, mul_zero, mul_one, zero_add]
    · rw [if_neg hkm, if_neg hkL, mul_zero, mul_zero, add_zero, hr k hkm hkL]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_decomp

/-- **Key step.** With `Stab(J, m)`, an element `t ∈ Q` fixing `r` (supported on `{m, L}`,
`r m ≠ 0`) lies in `Z ⊔ Q^m`. -/
theorem fnWide_mem_ZQm (hmL : m ≠ L) {K : Finset I} (hmK : m ∈ K) (hLK : L ∉ K)
    (hStab : fnWide_Stab F (K.erase m) m) {r : I → Polynomial F} (hr : fnWide_Supp m L r)
    (hrm : r m ≠ 0) {t : SteinbergGroup I (Polynomial F)} (ht : t ∈ fnQ F K L)
    (htr : act t r = r) : t ∈ fnZ F ⊔ fnWide_Qm F K m L := by
  have hLe : ∀ j : I, j ∈ K → j ≠ L := fun j hj e => hLK (by rw [← e]; exact hj)
  obtain ⟨s, hs, v, hv, rfl⟩ := fn_SV_decomp hLK ht
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
    rw [← fnWide_decomp hmL hr]
    exact htr
  rw [fnWide_act_lin, hsE] at h2
  have h3 := add_right_cancel h2
  have hsm : act s (unitVec m) = unitVec m := funext fun k => by
    have h4 := congrFun h3 k
    simp only [Pi.smul_apply, smul_eq_mul] at h4
    exact mul_left_cancel₀ hrm h4
  rw [x_zero, one_mul]
  exact Subgroup.mul_mem _ (fnWide_S_mem_ZQm hmK hStab hs hsm)
    (Subgroup.mem_sup_right (rootSpan_mono (p := fun i j => i = L ∧ j ∈ K.erase m)
      (q := fun i j => i ∈ insert L K ∧ j ∈ K.erase m)
      (fun _ _ _ hij => ⟨Finset.mem_insert.2 (Or.inl hij.1), hij.2⟩) hv'))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_mem_ZQm

/-- **The core check.** `σ₀(r)⁻¹ t σ₀(r) ∈ Z ⊔ Q` for `t ∈ Q` fixing `r` (supported on
`{m, L}`), given `Stab(J, m)`. -/
theorem fnWide_core (hmL : m ≠ L) {K : Finset I} (hmK : m ∈ K) (hLK : L ∉ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) (hStab : fnWide_Stab F (K.erase m) m)
    {r : I → Polynomial F} (hr : fnWide_Supp m L r) {t : SteinbergGroup I (Polynomial F)}
    (ht : t ∈ fnQ F K L) (htr : act t r = r) :
    (fnSigma_sigma F m L hmL r)⁻¹ * t * fnSigma_sigma F m L hmL r ∈ fnZQ F K L := by
  by_cases hrm : r m = 0
  · rw [fnSigma_sigma, hrm, fnSigma_pair_zero]
    by_cases hu : IsUnit (r L)
    · obtain ⟨n, hmn, hLn⟩ := hthird m L
      obtain ⟨β, hβ⟩ := fnWeyl_exists_C_of_isUnit hu
      rw [hβ, fnWeyl_tau_C hmL, inv_inv]
      exact fn_mem_ZQ_of_mem_Q (fnWide_Qr_le_Q K L (fieldTorus_conj_rootSpan m L n hmL hmn hLn
        (fun i j => i ∈ insert L K ∧ j ∈ K) β (fnWide_Q_le_Qr K L ht)))
    · rw [fnSigma_tau, if_neg (show r L ≠ 1 from fun e => hu (by rw [e]; exact isUnit_one)),
        dif_neg hu, inv_one, one_mul, mul_one]
      exact fn_mem_ZQ_of_mem_Q ht
  · obtain ⟨z, hz, u, hu, rfl⟩ :=
      fnWide_Zsup_decomp hthird (fnWide_mem_ZQm hmL hmK hLK hStab hr hrm ht htr)
    have h := fnWide_Gml_conj_Qm hmK hLK (Subgroup.inv_mem _ (fnWide_sigma0_mem hmL r)) hu
    rw [inv_inv] at h
    have hc := fnZ_central hthird hz (fnSigma_sigma F m L hmL r)⁻¹
    have e : (fnSigma_sigma F m L hmL r)⁻¹ * (z * u) * fnSigma_sigma F m L hmL r =
        z * ((fnSigma_sigma F m L hmL r)⁻¹ * u * fnSigma_sigma F m L hmL r) := by
      calc (fnSigma_sigma F m L hmL r)⁻¹ * (z * u) * fnSigma_sigma F m L hmL r
          = ((fnSigma_sigma F m L hmL r)⁻¹ * z) * u * fnSigma_sigma F m L hmL r := by group
        _ = (z * (fnSigma_sigma F m L hmL r)⁻¹) * u * fnSigma_sigma F m L hmL r := by rw [← hc]
        _ = z * ((fnSigma_sigma F m L hmL r)⁻¹ * u * fnSigma_sigma F m L hmL r) := by group
    rw [e]
    exact Subgroup.mul_mem _ (fn_mem_ZQ_of_mem_Z hz) (fn_mem_ZQ_of_mem_Q (fnWide_Qm_le_Q K m L h))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWide_core

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
