import GroupApproximation.GroupTheory.HigmanThompson.PLMoves
import GroupApproximation.GroupTheory.HigmanThompson.CompactRangeB
import GroupApproximation.Meta.AxiomGuard

/-!
# `Rstab_{F_n}([a, b]) ≅ F_n`

Hyde–Lodha, Lemma 3.3 (second half): "for each `a, b ∈ [0,1] ∩ ℤ[1/n]`, `a < b`, it holds that
`Rstab_{F_n}([a,b]) ≅ F_n`", through a piecewise linear map `[a, b] → [0, m]` and Brown's
Proposition 4.1.

Here `rstab m a b` is the group of elements of `PLGroup n (n^ℤ)`, `n = m + 2`, fixing `(-∞, a]` and
`[b, ∞)` (for homeomorphisms, "support in `[a, b]`").  Conjugation by the chart `t ↦ n^N (t - a)`
identifies it with `compactF m k`, `k = n^N (b - a)` (`rstabEquivCompactF`), and Brown's isomorphism
`geoFEquivCompactF` identifies every `compactF m k`, `k ≥ 1`, with `F_n = compactF m 1`.
-/

namespace GroupApproximation
namespace HigmanThompson

variable (m : ℕ)

/-- `Rstab([a, b])`: elements of `PLGroup n (n^ℤ)` fixing `(-∞, a]` and `[b, ∞)`. -/
def rstab (a b : ℚ) : Subgroup (Equiv.Perm ℚ) where
  carrier := {f | f ∈ PLGroup (m + 2) (powSlopes m) ∧ (∀ t : ℚ, t ≤ a → f t = t) ∧
    ∀ t : ℚ, b ≤ t → f t = t}
  one_mem' := ⟨(PLGroup (m + 2) (powSlopes m)).one_mem, fun _ _ => rfl, fun _ _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨hf, hf0, hf1⟩ ⟨hg, hg0, hg1⟩
    refine ⟨(PLGroup (m + 2) (powSlopes m)).mul_mem hf hg, fun t ht => ?_, fun t ht => ?_⟩
    · show f (g t) = t
      rw [hg0 t ht, hf0 t ht]
    · show f (g t) = t
      rw [hg1 t ht, hf1 t ht]
  inv_mem' := by
    rintro f ⟨hf, hf0, hf1⟩
    refine ⟨(PLGroup (m + 2) (powSlopes m)).inv_mem hf, fun t ht => ?_, fun t ht => ?_⟩
    · rw [Equiv.Perm.inv_eq_iff_eq, hf0 t ht]
    · rw [Equiv.Perm.inv_eq_iff_eq, hf1 t ht]

variable {m}

section Conj

variable {N k : ℕ} {a b : ℚ} (ha : a ∈ Grid (m + 2) N)
  (hk : ((m : ℚ) + 2) ^ N * (b - a) = k)

include ha hk in
theorem conj_mem_compactF {f : Equiv.Perm ℚ} (hf : f ∈ rstab m a b) :
    scalePerm m N a * f * (scalePerm m N a)⁻¹ ∈ compactF m k := by
  obtain ⟨hfP, hf0, hf1⟩ := hf
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ N := pow_pos mTwo_pos N
  have hinv : ((m : ℚ) + 2) ^ N * (((m : ℚ) + 2) ^ N)⁻¹ = 1 := mul_inv_cancel₀ hpos.ne'
  have hA := scalePerm_mem m N ha
  refine ⟨(PLGroup (m + 2) (powSlopes m)).mul_mem
    ((PLGroup (m + 2) (powSlopes m)).mul_mem hA hfP) ((PLGroup (m + 2) (powSlopes m)).inv_mem hA),
    fun t ht => ?_, fun t ht => ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    have h1 : (scalePerm m N a)⁻¹ t ≤ a := by
      rw [scalePerm_inv_apply]
      have h := mul_nonpos_of_nonpos_of_nonneg ht (inv_pos.mpr hpos).le
      linarith
    rw [hf0 _ h1]
    exact Equiv.apply_symm_apply (scalePerm m N a) t
  · simp only [Equiv.Perm.mul_apply]
    have h1 : b ≤ (scalePerm m N a)⁻¹ t := by
      rw [scalePerm_inv_apply]
      have hb : b = a + (k : ℚ) * (((m : ℚ) + 2) ^ N)⁻¹ := by
        rw [← hk]
        linear_combination (a - b) * hinv
      have h := mul_le_mul_of_nonneg_right ht (inv_pos.mpr hpos).le
      linarith
    rw [hf1 _ h1]
    exact Equiv.apply_symm_apply (scalePerm m N a) t

include ha hk in
theorem conj_inv_mem_rstab {g : Equiv.Perm ℚ} (hg : g ∈ compactF m k) :
    (scalePerm m N a)⁻¹ * g * scalePerm m N a ∈ rstab m a b := by
  obtain ⟨hgP, hg0, hg1⟩ := hg
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ N := pow_pos mTwo_pos N
  have hA := scalePerm_mem m N ha
  refine ⟨(PLGroup (m + 2) (powSlopes m)).mul_mem
    ((PLGroup (m + 2) (powSlopes m)).mul_mem ((PLGroup (m + 2) (powSlopes m)).inv_mem hA) hgP) hA,
    fun t ht => ?_, fun t ht => ?_⟩
  · simp only [Equiv.Perm.mul_apply]
    have h1 : scalePerm m N a t ≤ 0 := by
      rw [scalePerm_apply]
      exact mul_nonpos_of_nonneg_of_nonpos hpos.le (sub_nonpos.mpr ht)
    rw [hg0 _ h1]
    exact Equiv.symm_apply_apply (scalePerm m N a) t
  · simp only [Equiv.Perm.mul_apply]
    have h1 : (k : ℚ) ≤ scalePerm m N a t := by
      rw [scalePerm_apply, ← hk]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht a) hpos.le
    rw [hg1 _ h1]
    exact Equiv.symm_apply_apply (scalePerm m N a) t

/-- **`Rstab([a, b]) ≅ F_{n,k}`**, by conjugating with `t ↦ n^N (t - a)`. -/
noncomputable def rstabEquivCompactF : rstab m a b ≃* compactF m k where
  toFun f := ⟨scalePerm m N a * f * (scalePerm m N a)⁻¹, conj_mem_compactF ha hk f.2⟩
  invFun g := ⟨(scalePerm m N a)⁻¹ * g * scalePerm m N a, conj_inv_mem_rstab ha hk g.2⟩
  left_inv f := by
    apply Subtype.ext
    show (scalePerm m N a)⁻¹ * (scalePerm m N a * f * (scalePerm m N a)⁻¹) * scalePerm m N a = f
    group
  right_inv g := by
    apply Subtype.ext
    show scalePerm m N a * ((scalePerm m N a)⁻¹ * g * scalePerm m N a) * (scalePerm m N a)⁻¹ = g
    group
  map_mul' f g := by
    apply Subtype.ext
    show scalePerm m N a * ((f : Equiv.Perm ℚ) * g) * (scalePerm m N a)⁻¹ =
      (scalePerm m N a * f * (scalePerm m N a)⁻¹) * (scalePerm m N a * g * (scalePerm m N a)⁻¹)
    group

end Conj

/-- **Hyde–Lodha, Lemma 3.3 (second half).**  For `a < b` in `ℤ[1/n]`, `Rstab([a, b]) ≅ F_n`. -/
theorem rstab_equiv_compactF_one {a b : ℚ} (ha : ∃ M, a ∈ Grid (m + 2) M)
    (hb : ∃ M, b ∈ Grid (m + 2) M) (hab : a < b) : Nonempty (rstab m a b ≃* compactF m 1) := by
  obtain ⟨Ma, hMa⟩ := ha
  obtain ⟨Mb, hMb⟩ := hb
  have haN : a ∈ Grid (m + 2) (max Ma Mb) := grid_mono (le_max_left Ma Mb) hMa
  have hbN : b ∈ Grid (m + 2) (max Ma Mb) := grid_mono (le_max_right Ma Mb) hMb
  obtain ⟨j, hj⟩ := grid_sub hbN haN
  have hcast : (((m + 2 : ℕ) : ℚ)) = (m : ℚ) + 2 := by push_cast; ring
  rw [hcast] at hj
  have hpos : (0 : ℚ) < ((m : ℚ) + 2) ^ (max Ma Mb) := pow_pos mTwo_pos _
  have hj0 : (0 : ℚ) < (j : ℚ) := by
    rw [← hj]
    exact mul_pos (sub_pos.mpr hab) hpos
  have hj0' : 0 < j := by exact_mod_cast hj0
  obtain ⟨k, hkj⟩ := Int.eq_ofNat_of_zero_le hj0'.le
  have hk1 : 1 ≤ k := by omega
  have hk : ((m : ℚ) + 2) ^ (max Ma Mb) * (b - a) = k := by
    rw [mul_comm, hj, hkj, Int.cast_natCast]
  exact ⟨(rstabEquivCompactF haN hk).trans
    ((geoFEquivCompactF m k hk1).symm.trans (geoFEquivCompactF m 1 le_rfl))⟩

/-- `Rstab([a, b])` is finitely presented. -/
theorem isFinitelyPresented_rstab {a b : ℚ} (ha : ∃ M, a ∈ Grid (m + 2) M)
    (hb : ∃ M, b ∈ Grid (m + 2) M) (hab : a < b) : Group.IsFinitelyPresented (rstab m a b) := by
  obtain ⟨e⟩ := rstab_equiv_compactF_one ha hb hab
  haveI := compactF_isFinitelyPresented m 1 le_rfl
  exact Group.IsFinitelyPresented.equiv e.symm

/-- `Rstab([a, b]) ≤ F_n` for `0 ≤ a` and `b ≤ 1`. -/
theorem rstab_le_compactF_one {a b : ℚ} (ha : 0 ≤ a) (hb : b ≤ 1) : rstab m a b ≤ compactF m 1 := by
  rintro f ⟨hfP, hf0, hf1⟩
  refine ⟨hfP, fun t ht => hf0 t (le_trans ht ha), fun t ht => hf1 t ?_⟩
  have h : (1 : ℚ) ≤ t := by exact_mod_cast ht
  linarith

#audit_axioms GroupApproximation.HigmanThompson.rstab_equiv_compactF_one
#audit_axioms GroupApproximation.HigmanThompson.isFinitelyPresented_rstab

end HigmanThompson
end GroupApproximation
