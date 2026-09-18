import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnColimit.EmbeddingLimit
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnDegZero.Fock
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVSkewLaurentK2.Interface
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# `CohnLimit` is not ultramatricial (lane sk-lv-01, LOUD)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii; Ara–Brustenga–Cortiñas,
Münster J. Math. 2 (2009), Thm 3.6, Step 3.  The suggested attack on `StableK2Trivial CohnLimit`
("exhibit the finite stages of `CohnLimit` inside rings already known to have stable `K₂ = 0`",
via `LVCohnK2.stableK2Trivial_of_isUltramatricialF2`) CANNOT work.  Every stage contains a copy of
`C = C_2(𝔽₂)`, and `C` is not directly finite: `y₀ x₀ = 1` but `x₀ y₀ ≠ 1`.  Finite products of
matrix rings over `𝔽₂`, and hence ultramatricial `𝔽₂`-rings, are directly finite.

* `skCohnLimK2_cx_mul_cy_ne_one`: `x₀ y₀ ≠ 1` in `C` (else `y₁ = y₁ x₀ y₀ = 0` and `P = 0`);
* `skCohnLimK2_mul_eq_one_comm_of_isUltramatricialF2`: ultramatricial rings are directly finite;
* `skCohnLimK2_not_isUltramatricialF2`: `¬ IsUltramatricialF2 CohnLimit`.
-/

namespace GroupApproximation.Full.LVCohnColimit

noncomputable section

/-- `x₀ y₀ ≠ 1` in `C_2(𝔽₂)`: otherwise `y₁ = y₁ x₀ y₀ = 0`, and then the vacuum projection
`P = 1 - x₀ y₀ - x₁ y₁` vanishes, contradicting `LVCohnDegZero.cohnP_ne_zero`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_cx_mul_cy_ne_one :
    LVCohnRelK1.cx false * LVCohnRelK1.cy false ≠ 1 := by
  intro h
  have hy : LVCohnRelK1.cy true = 0 := by
    rw [← mul_one (LVCohnRelK1.cy true), ← h, ← mul_assoc, LVCohnRelK1.y1_x0, zero_mul]
  apply LVCohnDegZero.cohnP_ne_zero
  rw [LVCohnRelK1.cohnP_def, h, hy, mul_zero, sub_zero, sub_self]

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_cx_mul_cy_ne_one

/-- Finite products of matrix rings over `𝔽₂` are directly finite.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_pi_mul_eq_one_comm (k : ℕ) (d : Fin (k + 1) → ℕ)
    {a b : (j : Fin (k + 1)) → Matrix (Fin (d j)) (Fin (d j)) (ZMod 2)} (h : a * b = 1) :
    b * a = 1 := by
  funext j
  have hj := congrFun h j
  rw [Pi.mul_apply, Pi.one_apply] at hj
  rw [Pi.mul_apply, Pi.one_apply]
  exact mul_eq_one_comm.mp hj

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_pi_mul_eq_one_comm

/-- Ultramatricial `𝔽₂`-rings are directly finite: `v u = 1` implies `u v = 1`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_mul_eq_one_comm_of_isUltramatricialF2 {S : Type*} [Ring S]
    (hS : LVSkewLaurentK2.IsUltramatricialF2 S) {u v : S} (h : v * u = 1) : u * v = 1 := by
  classical
  obtain ⟨k, d, T, hsT, ⟨e⟩⟩ := hS {u, v}
  have hu : u ∈ T := hsT (Finset.mem_coe.mpr (Finset.mem_insert_self u {v}))
  have hv : v ∈ T :=
    hsT (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_singleton_self v)))
  let u' : T := ⟨u, hu⟩
  let v' : T := ⟨v, hv⟩
  have h1 : v' * u' = 1 := Subtype.ext h
  have h2 : e v' * e u' = 1 := (map_mul e v' u').symm.trans ((congrArg e h1).trans (map_one e))
  have h3 : e u' * e v' = 1 := skCohnLimK2_pi_mul_eq_one_comm k d h2
  have h4 : u' * v' = 1 := e.injective ((map_mul e u' v').trans (h3.trans (map_one e).symm))
  exact congrArg Subtype.val h4

#audit_axioms
  GroupApproximation.Full.LVCohnColimit.skCohnLimK2_mul_eq_one_comm_of_isUltramatricialF2

/-- **LOUD: `CohnLimit` is not ultramatricial.**  With `u = ι₀(x₀, 1)` and `v = ι₀(y₀, 1)` we
have `v u = 1` but `u v ≠ 1`, because `ι₀` is injective and `x₀ y₀ ≠ 1`.  So the finite stages of
`CohnLimit` do not lie in products of matrix rings over `𝔽₂`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem skCohnLimK2_not_isUltramatricialF2 :
    ¬ LVSkewLaurentK2.IsUltramatricialF2 CohnLimit := by
  intro hS
  have hvu : cohnLimitOf 0 (LVCohnRelK1.cy false, 1) *
      cohnLimitOf 0 (LVCohnRelK1.cx false, 1) = 1 := by
    rw [← map_mul (cohnLimitOf 0), ← map_one (cohnLimitOf 0)]
    exact congrArg (cohnLimitOf 0) (Prod.ext LVCohnRelK1.y0_x0 (mul_one (1 : ZMod 2)))
  have huv := skCohnLimK2_mul_eq_one_comm_of_isUltramatricialF2 hS hvu
  rw [← map_mul (cohnLimitOf 0), ← map_one (cohnLimitOf 0)] at huv
  have hfst := congrArg Prod.fst (cohnLimitOf_injective 0 huv)
  exact skCohnLimK2_cx_mul_cy_ne_one hfst

#audit_axioms GroupApproximation.Full.LVCohnColimit.skCohnLimK2_not_isUltramatricialF2

end

end GroupApproximation.Full.LVCohnColimit
