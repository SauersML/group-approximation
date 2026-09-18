import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoJResCocycle
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegWeyl
import GroupApproximation.Meta.AxiomGuard

/-!
# The residual root check, part 2: the Weyl elements `ω = w_mj(1)` and `W = w_mL(1)`

Lane `bh-met-94e`.  Notation of `ElemFPK2PolyNagaoJResCocycle`.

* `k2PolyNagaoJRes_om_eq`: `w_ab(1) = x_ab(1) x_ba(-1) x_ab(1)`.
* `k2PolyNagaoJRes_om_m`, `_om_j`, `_om_other`: `ω = w_mj(1)` sends `v` to the vector with
  `m`-coordinate `v_j`, `j`-coordinate `-v_m` and all other coordinates unchanged.
* `k2PolyNagaoJRes_om_mem_Q`: `ω ∈ S_K ≤ Q` for `m, j ∈ K`.
* `k2PolyNagaoJRes_xjL_eq`: `x_jL(c) = ω⁻¹ x_mL(c) ω`.
* `k2PolyNagaoJRes_W_mem_G`, `k2PolyNagaoJRes_W_conj_mem_Q`: `W = w_mL(1) ∈ G` and
  `W x_mL(c) W⁻¹ = x_Lm(b) ∈ V ≤ Q`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul
  act_x_apply x_mem_rootSpan)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w w_conj_x_row_j)

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- `act x_ik(c)` at the row `i`: `v_i + c v_k`. -/
theorem k2PolyNagaoJRes_act_x_self {i k : I} (hik : i ≠ k) (c : Polynomial (ZMod p))
    (v : I → Polynomial (ZMod p)) : act (x i k hik c) v i = v i + c * v k := by
  rw [act_x_apply, if_pos (rfl : i = i)]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_act_x_self

omit [Fact p.Prime] in
/-- `w_ab(1) = x_ab(1) x_ba(-1) x_ab(1)`. -/
theorem k2PolyNagaoJRes_om_eq {m j : I} (hmj : m ≠ j) :
    w m j hmj (1 : (Polynomial (ZMod p))ˣ) =
      x m j hmj (1 : Polynomial (ZMod p)) * x j m hmj.symm (-1 : Polynomial (ZMod p)) *
        x m j hmj (1 : Polynomial (ZMod p)) := by
  simp only [w, inv_one, Units.val_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_om_eq

omit [Fact p.Prime] in
/-- `(ω v)_m = v_j`. -/
theorem k2PolyNagaoJRes_om_m {m j : I} (hmj : m ≠ j) (v : I → Polynomial (ZMod p)) :
    act (w m j hmj (1 : (Polynomial (ZMod p))ˣ)) v m = v j := by
  have a1 : act (x m j hmj (1 : Polynomial (ZMod p))) v m = v m + v j := by
    rw [k2PolyNagaoJRes_act_x_self, one_mul]
  have a2 : act (x m j hmj (1 : Polynomial (ZMod p))) v j = v j :=
    k2PolyNagaoWide_act_x_ne hmj 1 v hmj.symm
  have b1 : act (x j m hmj.symm (-1 : Polynomial (ZMod p)))
      (act (x m j hmj (1 : Polynomial (ZMod p))) v) m =
      act (x m j hmj (1 : Polynomial (ZMod p))) v m :=
    k2PolyNagaoWide_act_x_ne hmj.symm (-1) _ hmj
  have b2 : act (x j m hmj.symm (-1 : Polynomial (ZMod p)))
      (act (x m j hmj (1 : Polynomial (ZMod p))) v) j =
      act (x m j hmj (1 : Polynomial (ZMod p))) v j +
        -1 * act (x m j hmj (1 : Polynomial (ZMod p))) v m :=
    k2PolyNagaoJRes_act_x_self hmj.symm (-1) _
  rw [k2PolyNagaoJRes_om_eq, act_mul, act_mul, k2PolyNagaoJRes_act_x_self, b1, b2, a1, a2]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_om_m

omit [Fact p.Prime] in
/-- `(ω v)_j = -v_m`. -/
theorem k2PolyNagaoJRes_om_j {m j : I} (hmj : m ≠ j) (v : I → Polynomial (ZMod p)) :
    act (w m j hmj (1 : (Polynomial (ZMod p))ˣ)) v j = -v m := by
  have a1 : act (x m j hmj (1 : Polynomial (ZMod p))) v m = v m + v j := by
    rw [k2PolyNagaoJRes_act_x_self, one_mul]
  have a2 : act (x m j hmj (1 : Polynomial (ZMod p))) v j = v j :=
    k2PolyNagaoWide_act_x_ne hmj 1 v hmj.symm
  have b2 : act (x j m hmj.symm (-1 : Polynomial (ZMod p)))
      (act (x m j hmj (1 : Polynomial (ZMod p))) v) j =
      act (x m j hmj (1 : Polynomial (ZMod p))) v j +
        -1 * act (x m j hmj (1 : Polynomial (ZMod p))) v m :=
    k2PolyNagaoJRes_act_x_self hmj.symm (-1) _
  rw [k2PolyNagaoJRes_om_eq, act_mul, act_mul, k2PolyNagaoWide_act_x_ne hmj _ _ hmj.symm, b2,
    a1, a2]
  ring

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_om_j

omit [Fact p.Prime] in
/-- `(ω v)_l = v_l` for `l ∉ {m, j}`. -/
theorem k2PolyNagaoJRes_om_other {m j : I} (hmj : m ≠ j) (v : I → Polynomial (ZMod p))
    {l : I} (hlm : l ≠ m) (hlj : l ≠ j) :
    act (w m j hmj (1 : (Polynomial (ZMod p))ˣ)) v l = v l := by
  rw [k2PolyNagaoJRes_om_eq, act_mul, act_mul, k2PolyNagaoWide_act_x_ne hmj _ _ hlm,
    k2PolyNagaoWide_act_x_ne hmj.symm _ _ hlj, k2PolyNagaoWide_act_x_ne hmj _ _ hlm]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_om_other

/-- `ω = w_mj(1) ∈ S_K ≤ Q` for `m, j ∈ K`. -/
theorem k2PolyNagaoJRes_om_mem_Q {K : Finset I} {m j : I} (L : I) (hmj : m ≠ j) (hmK : m ∈ K)
    (hjK : j ∈ K) : w m j hmj (1 : (Polynomial (ZMod p))ˣ) ∈ k2PolyNF_Q p K L :=
  Subgroup.mem_sup_left (S := k2PolyDeg_S p K) (T := k2PolyDeg_V p K L)
    (k2PolyDeg_w_mem_rootSpan (q := fun a b => a ∈ K ∧ b ∈ K) m j hmj
      (1 : (Polynomial (ZMod p))ˣ) ⟨hmK, hjK⟩ ⟨hjK, hmK⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_om_mem_Q

omit [Fact p.Prime] in
/-- **The Weyl trick**: `x_jL(c) = ω⁻¹ x_mL(c) ω`. -/
theorem k2PolyNagaoJRes_xjL_eq {m j L : I} (hmj : m ≠ j) (hmL : m ≠ L) (hjL : j ≠ L)
    (c : Polynomial (ZMod p)) :
    x j L hjL c =
      (w m j hmj (1 : (Polynomial (ZMod p))ˣ))⁻¹ * x m L hmL c *
        w m j hmj (1 : (Polynomial (ZMod p))ˣ) := by
  have hc := w_conj_x_row_j m j L hmj hmL hjL (1 : (Polynomial (ZMod p))ˣ) c
  rw [Units.val_one, one_mul] at hc
  rw [← hc]
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_xjL_eq

/-- `W = w_mL(1) ∈ G`. -/
theorem k2PolyNagaoJRes_W_mem_G {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K) :
    w m L hmL (1 : (Polynomial (ZMod p))ˣ) ∈ k2PolyDeg_G p K L :=
  k2PolyDeg_w_mem_rootSpan (q := fun a b => a ∈ insert L K ∧ b ∈ insert L K) m L hmL
    (1 : (Polynomial (ZMod p))ˣ) ⟨Finset.mem_insert_of_mem hmK, Finset.mem_insert_self L K⟩
    ⟨Finset.mem_insert_self L K, Finset.mem_insert_of_mem hmK⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_W_mem_G

/-- `W x_mL(c) W⁻¹ = x_Lm(b) ∈ V ≤ Q`. -/
theorem k2PolyNagaoJRes_W_conj_mem_Q {K : Finset I} {m L : I} (hmL : m ≠ L) (hmK : m ∈ K)
    (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) (c : Polynomial (ZMod p)) :
    w m L hmL (1 : (Polynomial (ZMod p))ˣ) * x m L hmL c *
        (w m L hmL (1 : (Polynomial (ZMod p))ˣ))⁻¹ ∈ k2PolyNF_Q p K L := by
  obtain ⟨b, hb⟩ :=
    k2PolyDeg_w_conj_exists m L m L hmL hmL (hthird m L) (1 : (Polynomial (ZMod p))ˣ) c
  rw [hb]
  refine Subgroup.mem_sup_right (S := k2PolyDeg_S p K) (T := k2PolyDeg_V p K L) ?_
  exact x_mem_rootSpan (p := fun a b => a = L ∧ b ∈ K) _ b
    ⟨Equiv.swap_apply_left m L, by rw [Equiv.swap_apply_right]; exact hmK⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyNagaoJRes_W_conj_mem_Q

end GroupApproximation.BooneHigman.Metabelian.ElemFP
