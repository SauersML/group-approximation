import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoTorusPair
import GroupApproximation.Meta.AxiomGuard

/-!
# The odd-`p` Nagao torus, part 3: the torus interface for every prime

Lane `bh-met-94b`.  Closes gap (a) of lane 93v: `k2PolyNagaoJRed_TorusAt p` for every prime `p`.

* `k2PolyNagaoTorus_shift`: lane 93v's `k2PolyNagaoRoot_shift` without the hypothesis
  `(q r)_m = r_m`.  By `k2PolyNagaoRoot_m_unit`, `(q r)_m = γ r_m` with `γ ∈ F_pˣ`; the torus
  element `t = t_mi(γ) ∈ S_K` (third index `i ∈ K`) rescales `r` to `r' = t r` with
  `r'_m = (q r)_m`, `r'_L = r_L`; `_shift` applies to `(q t⁻¹, r')`, and the correction
  `σ₀(r')⁻¹ t σ₀(r) = pair(γ r_m, r_L)⁻¹ t_mi(γ) pair(r_m, r_L)` lies in `Q`
  (`k2PolyNagaoTorus_pair_mem_one`).
* `k2PolyNagaoTorus_check`: the check of `σ` at `x_mL(1)` at every supported orbit vector.
* `k2PolyNagaoTorus_torusAt`, `k2PolyNagaoTorus_torusIface`, `k2PolyNagaoTorus_torusAt_odd`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul unitVec)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl
  (h manuscriptSentence_projectionDiagonalElement)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- `t_mi(γ)` acts diagonally: `γ` at `m`, `γ⁻¹` at `i`, `1` elsewhere. -/
theorem k2PolyNagaoTorus_act_tmi {m L i : I} (hmL : m ≠ L) (hmi : m ≠ i) (hLi : L ≠ i)
    (γ : (ZMod p)ˣ) (r : I → Polynomial (ZMod p)) (k : I) :
    act (k2PolyDeg_torus p m i L hmi hmL hLi.symm γ) r k =
      (if k = m then
          ((Units.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p)).toMonoidHom γ :
            (Polynomial (ZMod p))ˣ) : Polynomial (ZMod p))
        else if k = i then
          (((Units.map (Polynomial.C : ZMod p →+* Polynomial (ZMod p)).toMonoidHom γ)⁻¹ :
            (Polynomial (ZMod p))ˣ) : Polynomial (ZMod p))
        else 1) * r k := by
  rw [k2PolyDeg_torus_apply]
  simp only [act]
  rw [manuscriptSentence_projectionDiagonalElement, Matrix.mulVec_diagonal]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_act_tmi

/-- **The shift, for every prime.**  For `q ∈ Q` and an orbit vector `r` supported on `{m, L}`
such that `q r` is supported on `{m, L}`: `σ₀(q r)⁻¹ q σ₀(r) ∈ Q`. -/
theorem k2PolyNagaoTorus_shift {K : Finset I} {m L i : I} (hmL : m ≠ L) (hmi : m ≠ i)
    (hLi : L ≠ i) (hmK : m ∈ K) (hiK : i ∈ K) (hLK : L ∉ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {r : I → Polynomial (ZMod p)} (hr : k2PolyNagaoWide_Supp m L r)
    (hro : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = r)
    {q : SteinbergGroup I (Polynomial (ZMod p))} (hq : q ∈ k2PolyNF_Q p K L)
    (hs : k2PolyNagaoWide_Supp m L (act q r)) :
    (k2PolyNagaoSigma_sigma p m L hmL (act q r))⁻¹ * q * k2PolyNagaoSigma_sigma p m L hmL r ∈
      k2PolyNF_Q p K L := by
  obtain ⟨c, hc, hcm⟩ := k2PolyNagaoRoot_m_unit hmL hLK hq hr hs
  obtain ⟨γ, rfl⟩ := k2PolyNagaoWeyl_exists_C_of_isUnit hc
  have hA := k2PolyNagaoTorus_act_tmi hmL hmi hLi γ r
  have h0Q : k2PolyDeg_torus p m i L hmi hmL hLi.symm γ ∈ k2PolyNF_Q p K L :=
    Subgroup.mem_sup_left (S := k2PolyDeg_S p K) (T := k2PolyDeg_V p K L)
      (k2PolyNagaoTorus_tmi_mem_S hmL hmi hLi hmK hiK γ)
  have hr'm : act (k2PolyDeg_torus p m i L hmi hmL hLi.symm γ) r m =
      Polynomial.C (γ : ZMod p) * r m := by
    have e := hA m
    rw [if_pos rfl] at e
    exact e
  have hr'L : act (k2PolyDeg_torus p m i L hmi hmL hLi.symm γ) r L = r L := by
    rw [hA L, if_neg hmL.symm, if_neg hLi, one_mul]
  have hr'S : k2PolyNagaoWide_Supp m L (act (k2PolyDeg_torus p m i L hmi hmL hLi.symm γ) r) :=
    fun k hkm hkL => by rw [hA k, if_neg hkm, hr k hkm hkL, mul_zero]
  have hr'o := k2PolyNF_orbit_act (k2PolyNagaoWide_Q_le_G K L h0Q) hro
  have hback : act (q * (k2PolyDeg_torus p m i L hmi hmL hLi.symm γ)⁻¹)
      (act (k2PolyDeg_torus p m i L hmi hmL hLi.symm γ) r) = act q r := by
    rw [← act_mul, inv_mul_cancel_right]
  have h1 := k2PolyNagaoRoot_shift hmL hmK hLK hthird hStab hr'S hr'o
    (Subgroup.mul_mem _ hq (Subgroup.inv_mem _ h0Q)) (by rw [hback]; exact hs)
    (by rw [hback, hcm, hr'm])
  rw [hback] at h1
  have e : k2PolyNagaoSigma_sigma p m L hmL (act (k2PolyDeg_torus p m i L hmi hmL hLi.symm γ) r) =
      k2PolyNagaoSigma_pair p m L hmL (Polynomial.C (γ : ZMod p) * r m) (r L) := by
    rw [k2PolyNagaoSigma_sigma, hr'm, hr'L]
  rw [e] at h1
  have h2 := k2PolyNagaoTorus_pair_mem_one hmL hmi hLi hmK hiK γ
    (k2PolyNagaoRoot_coprime hmL hr hro)
  have e2 : ∀ A B C D E : SteinbergGroup I (Polynomial (ZMod p)),
      A⁻¹ * (B * C⁻¹) * D * (D⁻¹ * C * E) = A⁻¹ * B * E := by
    intro A B C D E
    group
  have key := Subgroup.mul_mem _ h1 h2
  rw [e2] at key
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_shift

/-- The coset of `σ(u) = q_u σ₀(r_u)` against `σ₀(u)`, for every supported orbit vector `u`:
`σ₀(u)⁻¹ q_u σ₀(r_u) ∈ Q` (`k2PolyNagaoTorus_shift` at `q_u`, `r_u`). -/
theorem k2PolyNagaoTorus_sigma_supp {K : Finset I} {m L i : I} (hmL : m ≠ L) (hmi : m ≠ i)
    (hLi : L ≠ i) (hmK : m ∈ K) (hiK : i ∈ K) (hLK : L ∉ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {u : I → Polynomial (ZMod p)} (hu : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = u)
    (huS : k2PolyNagaoWide_Supp m L u) :
    (k2PolyNagaoSigma_sigma p m L hmL u)⁻¹ * k2PolyNagaoWide_qsel p K m L u *
        k2PolyNagaoSigma_sigma p m L hmL (k2PolyNagaoWide_rep p K m L u) ∈
      k2PolyNF_Q p K L := by
  have hr := (k2PolyNagaoWide_rep_spec (m := m) hmK hu).1
  have hq := k2PolyNagaoWide_qsel_spec (m := m) hmK hu
  have hro := k2PolyNF_orbit_act (k2PolyNagaoWide_Q_le_G K L (Subgroup.inv_mem _ hq.1)) hu
  rw [k2PolyNagaoWide_act_inv hq.2] at hro
  have h := k2PolyNagaoTorus_shift hmL hmi hLi hmK hiK hLK hthird hStab hr hro hq.1
    (by rw [hq.2]; exact huS)
  rw [hq.2] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_sigma_supp

/-- **The check, for every prime.**  The check of `σ = k2PolyNagaoWide_sigma` at `y = x_mL(1)`
holds at every orbit vector `v` supported on `{m, L}`, given a third index `i ∈ K`:
`σ(yv)⁻¹ y σ(v) = B₂⁻¹ (σ₀(yv)⁻¹ y σ₀(v)) B₁` with `B₁, B₂ ∈ Q` (`_sigma_supp`) and the middle
factor in `Q` (`k2PolyNagaoRoot_rank_one`). -/
theorem k2PolyNagaoTorus_check {K : Finset I} {m L i : I} (hmL : m ≠ L) (hmi : m ≠ i)
    (hLi : L ≠ i) (hmK : m ∈ K) (hiK : i ∈ K) (hLK : L ∉ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (hconst : ∀ g ∈ (ringMap (I := I) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range,
      g ∈ K2 I (Polynomial (ZMod p)) → g = 1)
    (hStab : k2PolyNagaoWide_Stab p (K.erase m) m)
    {v : I → Polynomial (ZMod p)} (hv : ∃ y ∈ k2PolyDeg_G p K L, act y (unitVec L) = v)
    (hS : k2PolyNagaoWide_Supp m L v) :
    (k2PolyNagaoWide_sigma p K m L hmL (act (x m L hmL (1 : Polynomial (ZMod p))) v))⁻¹ *
        x m L hmL (1 : Polynomial (ZMod p)) * k2PolyNagaoWide_sigma p K m L hmL v ∈
      k2PolyNF_Q p K L := by
  have hyG := k2PolyEuclid_x_mem_G hmL (1 : Polynomial (ZMod p))
    (Finset.mem_insert_of_mem hmK) (Finset.mem_insert_self L K)
  have hvy := k2PolyNF_orbit_act hyG hv
  have B1 := k2PolyNagaoTorus_sigma_supp hmL hmi hLi hmK hiK hLK hthird hStab hv hS
  have B2 := k2PolyNagaoTorus_sigma_supp hmL hmi hLi hmK hiK hLK hthird hStab hvy
    (k2PolyNagaoRoot_supp_x hmL hS)
  have R1 := k2PolyNagaoRoot_rank_one hmL hmK hthird hconst hS hv
  have e : ∀ a₁ s₁ a₂ s₂ y E F : SteinbergGroup I (Polynomial (ZMod p)),
      (E⁻¹ * a₂ * s₂)⁻¹ * (E⁻¹ * y * F) * (F⁻¹ * a₁ * s₁) = (a₂ * s₂)⁻¹ * y * (a₁ * s₁) := by
    intro a₁ s₁ a₂ s₂ y E F
    group
  have key := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ B2) R1) B1
  rw [e] at key
  exact key

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_check

/-- **Gap (a) of lane 93v closed: the torus interface at every prime `p`.** -/
theorem k2PolyNagaoTorus_torusAt : ∀ (p : ℕ) [Fact p.Prime], k2PolyNagaoJRed_TorusAt p := by
  intro p _ I _ _ K m L hmL hLK hmK him hthird hconst _ hJ v hv hS
  obtain ⟨i, hiK, hi⟩ := him
  have hLi : L ≠ i := fun e => hLK (by rw [e]; exact hiK)
  exact k2PolyNagaoTorus_check hmL (Ne.symm hi) hLi hmK hiK hLK hthird hconst hJ hv hS

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_torusAt

/-- **The torus interface** `k2PolyNagaoJRed_TorusIface`. -/
theorem k2PolyNagaoTorus_torusIface : k2PolyNagaoJRed_TorusIface :=
  k2PolyNagaoTorus_torusAt

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_torusIface

/-- The lane target in its stated form: the torus interface at every odd prime. -/
theorem k2PolyNagaoTorus_torusAt_odd :
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → k2PolyNagaoJRed_TorusAt p :=
  fun p _ _ => k2PolyNagaoTorus_torusAt p

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoTorus_torusAt_odd

end GroupApproximation.BooneHigman.Metabelian.ElemFP
