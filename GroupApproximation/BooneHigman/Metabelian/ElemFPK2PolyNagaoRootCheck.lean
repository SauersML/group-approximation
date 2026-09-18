import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoRootOrbit
import GroupApproximation.Meta.AxiomGuard

/-!
# The root check of the wide section, part 2: the supported case

Lane `bh-met-93v`.  Notation of `ElemFPK2PolyNagaoWideSigma`; `σ₀ = k2PolyNagaoSigma_sigma`,
`σ(v) = q_v σ₀(r_v)` (`k2PolyNagaoWide_sigma`), `y = x_mL(1)`.

* `k2PolyNagaoRoot_Q_mono`: `Q_{{m}} ≤ Q_K` for `m ∈ K`.
* `k2PolyNagaoRoot_rank_one`: `σ₀(y v)⁻¹ y σ₀(v) ∈ Q_K` for every supported `v` of the
  `G_K`-orbit (the rank-one Weyl check of lane 93d at `K = {m}`, via `_orbit_one`).
* `k2PolyNagaoRoot_Q_L`: for `q ∈ Q` and supported `r`, `(q r)_L = r_L + d r_m`.
* `k2PolyNagaoRoot_shift`: if moreover `q r` is supported with `(q r)_m = r_m`, then
  `q r = x_Lm(d) r` and `σ₀(q r)⁻¹ q σ₀(r) ∈ Q` (the `x_Lm` check and the core check).
* `k2PolyNagaoRoot_check_supp`: hence the check of `σ` at `y` holds at every supported orbit
  vector `v` whose representatives `r_v`, `r_{yv}` keep the `m`-coordinate.
* `k2PolyNagaoRoot_m_unit`, `_rep_m`: `(q r)_m = c r_m` with `c` a unit; so when
  `(ZMod p)ˣ` is trivial (`p = 2`), the representatives always keep the `m`-coordinate.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul
  act_x_apply unitVec unitVec_apply rootSpan_mono exists_split act_eq_self_of_rootSpan
  act_apply_of_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- `Q_{{m}} ≤ Q_K` for `m ∈ K`. -/
theorem k2PolyNagaoRoot_Q_mono {K : Finset I} {m L : I} (hmK : m ∈ K)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyNF_Q p {m} L) :
    g ∈ k2PolyNF_Q p K L := by
  have hpq : ∀ i j : I, i ≠ j → (i ∈ insert L ({m} : Finset I) ∧ j ∈ ({m} : Finset I)) →
      (i ∈ insert L K ∧ j ∈ K) := fun i j _ hij => by
    refine ⟨?_, by rw [Finset.mem_singleton.1 hij.2]; exact hmK⟩
    rcases Finset.mem_insert.1 hij.1 with h | h
    · rw [h]; exact Finset.mem_insert_self L K
    · rw [Finset.mem_singleton.1 h]; exact Finset.mem_insert_of_mem hmK
  exact k2PolyNagaoWide_Qr_le_Q K L (rootSpan_mono
    (p := fun i j => i ∈ insert L ({m} : Finset I) ∧ j ∈ ({m} : Finset I))
    (q := fun i j => i ∈ insert L K ∧ j ∈ K) hpq (k2PolyNagaoWide_Q_le_Qr {m} L hg))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_Q_mono

/-- **The rank-one check.**  `σ₀(y v)⁻¹ y σ₀(v) ∈ Q_K` for every orbit vector `v` supported on
`{m, L}` (lane 93d's rank-one checks at `K = {m}`, transported by `_orbit_one`, `_Q_mono`). -/
theorem k2PolyNagaoRoot_rank_one {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    {v : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L v)
    (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v) :
    (k2PolyNagaoSigma_sigma p m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v))⁻¹ *
        x m L hmL (1 : Polynomial (ZMod p)) * k2PolyNagaoSigma_sigma p m L hmL v ∈
      k2PolyNF_Q p K L := by
  have hKm : ∀ i ∈ ({m} : Finset I), i = m := fun _ hi => Finset.mem_singleton.1 hi
  have hG := k2PolyNagaoSigma_gens_of_weyl hmL (Finset.mem_singleton_self m) hKm hthird
    (k2PolyNagaoWeyl_weylStatement p ({m} : Finset I) m L hmL (Finset.mem_singleton_self m)
      hKm hthird hconst)
  obtain ⟨-, hxmL, -⟩ := hG
  exact k2PolyNagaoRoot_Q_mono hmK (hxmL v (k2PolyNagaoRoot_orbit_one hmL hr hv))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_rank_one

/-- For `q ∈ Q` and `r` supported on `{m, L}`: `(q r)_L = r_L + d r_m` (write `q = s x_Lm(d) v'`
with `s ∈ S_K` fixing the `L`-row and `v'` fixing `r`). -/
theorem k2PolyNagaoRoot_Q_L {K : Finset I} {m L : I} (hmL : m ≠ L) (hLK : L ∉ K)
    {q : SteinbergGroup I (Polynomial (ZMod p))} (hq : q ∈ k2PolyNF_Q p K L)
    {r : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L r) :
    ∃ d : Polynomial (ZMod p), act q r L = r L + d * r m := by
  have hLe : ∀ j : I, j ∈ K → j ≠ L := fun j hj e => hLK (by rw [← e]; exact hj)
  obtain ⟨s, hs, v, hv, rfl⟩ := k2PolyDeg_SV_decomp hLK hq
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
  refine ⟨d, ?_⟩
  rw [act_mul, act_mul, hv'r, hsL, act_x_apply, if_pos rfl]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_Q_L

/-- **The shift.**  For `q ∈ Q` and an orbit vector `r` supported on `{m, L}` such that `q r` is
supported on `{m, L}` with `(q r)_m = r_m`: `q r = x_Lm(d) r`, so `σ₀(q r)⁻¹ q σ₀(r) ∈ Q` (the
`x_Lm(d)` check times the core check of `x_Lm(d)⁻¹ q`, which fixes `r`). -/
theorem k2PolyNagaoRoot_shift {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {r : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L r)
    (hro : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = r)
    {q : SteinbergGroup I (Polynomial (ZMod p))} (hq : q ∈ k2PolyNF_Q p K L)
    (hs : k2PolyNagaoWide_Supp m L (act q r)) (hm : act q r m = r m) :
    (k2PolyNagaoSigma_sigma p m L hmL (act q r))⁻¹ * q * k2PolyNagaoSigma_sigma p m L hmL r ∈
      k2PolyNF_Q p K L := by
  obtain ⟨d, hd⟩ := k2PolyNagaoRoot_Q_L hmL hLK hq hr
  have hX : act (x L m hmL.symm d) r = act q r := by
    funext k
    rw [act_x_apply]
    by_cases hkL : k = L
    · rw [hkL, if_pos rfl, hd]
    · rw [if_neg hkL, add_zero]
      by_cases hkm : k = m
      · rw [hkm, hm]
      · rw [hr k hkm hkL, hs k hkm hkL]
  have h1 := k2PolyNagaoSigma_check_Lm (K := K) hmL hmK (hthird m L) d r hro
  rw [hX] at h1
  have h2 := k2PolyNagaoWide_core hmL hmK hLK hthird hStab hr
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (k2PolyNagaoSigma_x_mem_Q hmL hmK d)) hq)
    (by rw [act_mul]; exact k2PolyNagaoWide_act_inv hX)
  have e : ∀ A B C X : SteinbergGroup I (Polynomial (ZMod p)),
      A⁻¹ * X * C * (C⁻¹ * (X⁻¹ * B) * C) = A⁻¹ * B * C := by
    intro A B C X
    group
  have key := Subgroup.mul_mem _ h1 h2
  rw [e] at key
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_shift

/-- The coset of `σ(u) = q_u σ₀(r_u)` against `σ₀(u)`, for a supported orbit vector `u` whose
representative keeps the `m`-coordinate: `σ₀(u)⁻¹ q_u σ₀(r_u) ∈ Q` (`_shift` at `q_u`, `r_u`). -/
theorem k2PolyNagaoRoot_sigma_supp {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {u : I → Polynomial (ZMod p)} (hu : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = u)
    (huS : k2PolyNagaoWide_Supp m L u) (hum : k2PolyNagaoWide_rep p K m L u m = u m) :
    (k2PolyNagaoSigma_sigma p m L hmL u)⁻¹ * k2PolyNagaoWide_qsel p K m L u *
        k2PolyNagaoSigma_sigma p m L hmL (k2PolyNagaoWide_rep p K m L u) ∈
      k2PolyNF_Q p K L := by
  have hr := (k2PolyNagaoWide_rep_spec (m := m) hmK hu).1
  have hq := k2PolyNagaoWide_qsel_spec (m := m) hmK hu
  have hro := k2PolyNF_orbit_act (k2PolyNagaoWide_Q_le_G K L (Subgroup.inv_mem _ hq.1)) hu
  rw [k2PolyNagaoWide_act_inv hq.2] at hro
  have h := k2PolyNagaoRoot_shift hmL hmK hLK hthird hStab hr hro hq.1
    (by rw [hq.2]; exact huS) (by rw [hq.2]; exact hum.symm)
  rw [hq.2] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_sigma_supp

omit [Fact p.Prime] in
/-- `x_mL(1)` keeps the support `{m, L}`. -/
theorem k2PolyNagaoRoot_supp_x {m L : I} (hmL : m ≠ L) {v : I → Polynomial (ZMod p)}
    (hS : k2PolyNagaoWide_Supp m L v) :
    k2PolyNagaoWide_Supp m L (act (x m L hmL (1 : Polynomial (ZMod p))) v) := by
  intro k hkm hkL
  rw [act_x_apply, if_neg hkm, add_zero]
  exact hS k hkm hkL

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_supp_x

/-- **The supported check.**  The check of `σ = k2PolyNagaoWide_sigma` at `y = x_mL(1)` holds at
every orbit vector `v` supported on `{m, L}` whose representatives `r_v`, `r_{yv}` keep the
`m`-coordinate: `σ(yv)⁻¹ y σ(v) = B₂⁻¹ (σ₀(yv)⁻¹ y σ₀(v)) B₁` with `B₁, B₂ ∈ Q`
(`_sigma_supp`) and the middle factor in `Q` (`_rank_one`). -/
theorem k2PolyNagaoRoot_check_supp {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v)
    (hS : k2PolyNagaoWide_Supp m L v) (h1 : k2PolyNagaoWide_rep p K m L v m = v m)
    (h2 : k2PolyNagaoWide_rep p K m L (act (x m L hmL (1 : Polynomial (ZMod p))) v) m =
      act (x m L hmL (1 : Polynomial (ZMod p))) v m) :
    (k2PolyNagaoWide_sigma p K m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v))⁻¹ *
        x m L hmL (1 : Polynomial (ZMod p)) * k2PolyNagaoWide_sigma p K m L hmL v ∈
      k2PolyNF_Q p K L := by
  have hyG := k2PolyEuclid_x_mem_G hmL (1 : Polynomial (ZMod p))
    (Finset.mem_insert_of_mem hmK) (Finset.mem_insert_self L K)
  have hvy := k2PolyNF_orbit_act hyG hv
  have B1 := k2PolyNagaoRoot_sigma_supp hmL hmK hLK hthird hStab hv hS h1
  have B2 := k2PolyNagaoRoot_sigma_supp hmL hmK hLK hthird hStab hvy
    (k2PolyNagaoRoot_supp_x hmL hS) h2
  have R1 := k2PolyNagaoRoot_rank_one hmL hmK hthird hconst hS hv
  have e : ∀ a₁ s₁ a₂ s₂ y E F : SteinbergGroup I (Polynomial (ZMod p)),
      (E⁻¹ * a₂ * s₂)⁻¹ * (E⁻¹ * y * F) * (F⁻¹ * a₁ * s₁) = (a₂ * s₂)⁻¹ * y * (a₁ * s₁) := by
    intro a₁ s₁ a₂ s₂ y E F
    group
  have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ B2) R1) B1
  rw [e] at key
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_check_supp

/-- **The torus factor.**  For `q ∈ Q` and `r`, `q r` both supported on `{m, L}`:
`(q r)_m = c r_m` with `c` a unit.  Write `q = s v` (`s ∈ S_K`, `v ∈ V`); `v` moves only the
`L`-row, and `s e_m = t` with `r_m t` supported on `{m, L}`, so `t = t_m e_m` and
`s⁻¹ (t_m e_m) = e_m` makes `t_m` a unit. -/
theorem k2PolyNagaoRoot_m_unit {K : Finset I} {m L : I} (hmL : m ≠ L) (hLK : L ∉ K)
    {q : SteinbergGroup I (Polynomial (ZMod p))} (hq : q ∈ k2PolyNF_Q p K L)
    {r : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L r)
    (hs : k2PolyNagaoWide_Supp m L (act q r)) :
    ∃ c : Polynomial (ZMod p), IsUnit c ∧ act q r m = c * r m := by
  have hLe : ∀ j : I, j ∈ K → j ≠ L := fun j hj e => hLK (by rw [← e]; exact hj)
  obtain ⟨s, hs0, v, hv, rfl⟩ := k2PolyDeg_SV_decomp hLK hq
  obtain ⟨r', hr'⟩ : ∃ r' : I → Polynomial (ZMod p), act v r = r' := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : I → Polynomial (ZMod p), act s (unitVec m) = t := ⟨_, rfl⟩
  have hr'k : ∀ k : I, k ≠ L → r' k = r k := fun k hk => by
    rw [← hr']
    exact act_apply_of_rootSpan (p := fun i j => i = L ∧ j ∈ K)
      (fun i _ h e => hk (e.symm.trans h.1)) hv r
  have hr'S : k2PolyNagaoWide_Supp m L r' := by
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
    rw [congrArg (act s) (k2PolyNagaoWide_decomp hmL hr'S), k2PolyNagaoWide_act_lin, hsE, ht,
      hr'k m hmL]
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
  have hinv := k2PolyNagaoWide_act_inv ht
  rw [htm] at hinv
  have hsm : act s⁻¹ (t m • unitVec m) = t m • act s⁻¹ (unitVec m) := by
    simp only [act, Matrix.mulVec_smul]
  rw [hsm] at hinv
  have h := congrFun hinv m
  rw [Pi.smul_apply, smul_eq_mul, unitVec_apply, if_pos rfl] at h
  exact IsUnit.of_mul_eq_one _ h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_m_unit

/-- When `(ZMod p)ˣ` is trivial (`p = 2`), the chosen representative of a supported orbit
vector keeps the `m`-coordinate (`_m_unit`: the unit factor is a constant, hence `1`). -/
theorem k2PolyNagaoRoot_rep_m {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hLK : L ∉ K) (h1 : ∀ β : (ZMod p)ˣ, β = 1)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v)
    (hS : k2PolyNagaoWide_Supp m L v) : k2PolyNagaoWide_rep p K m L v m = v m := by
  have hr := (k2PolyNagaoWide_rep_spec (m := m) hmK hv).1
  have hq := k2PolyNagaoWide_qsel_spec (m := m) hmK hv
  obtain ⟨c, hc, e⟩ := k2PolyNagaoRoot_m_unit hmL hLK hq.1 hr (by rw [hq.2]; exact hS)
  obtain ⟨β, rfl⟩ := k2PolyNagaoWeyl_exists_C_of_isUnit hc
  rw [hq.2, h1 β, Units.val_one, map_one, one_mul] at e
  exact e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoRoot_rep_m

end GroupApproximation.BooneHigman.Metabelian.ElemFP
