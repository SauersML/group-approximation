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
