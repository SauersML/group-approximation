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
