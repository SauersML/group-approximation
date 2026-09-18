import Mathlib.Data.Nat.Factorial.Basic

/-!
# The universal UHF algebra `Q`: block indices

Lane `TWWSch3d5a` (work order `WO-TWWSchafhauser-3d-5`, part (a)).  This is the
first construction file for `UHFInterface.lean`.

For `m ≤ n` the building block `M_{m!}` sits unitally inside `M_{n!}` as
`a ↦ a ⊗ 1_d` with `d = n!/m!` (Glimm; Davidson, *C⋆-algebras by example*,
Ch. III).  Here we fix the combinatorics of the identification
`Fin n! ≃ Fin m! × Fin d`, `i ↦ (i / d, i % d)`, and its compatibility with a
tower `k ≤ m ≤ n`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

/-- The multiplicity `n!/m!` of the block `M_{m!}` in `M_{n!}`. -/
def uhfBlockDim (m n : ℕ) : ℕ := n.factorial / m.factorial

theorem factorial_mul_uhfBlockDim {m n : ℕ} (h : m ≤ n) :
    m.factorial * uhfBlockDim m n = n.factorial :=
  Nat.mul_div_cancel' (Nat.factorial_dvd_factorial h)

theorem uhfBlockDim_pos {m n : ℕ} (h : m ≤ n) : 0 < uhfBlockDim m n := by
  apply Nat.pos_of_ne_zero
  intro h0
  have hmul := factorial_mul_uhfBlockDim h
  rw [h0, Nat.mul_zero] at hmul
  exact Nat.factorial_ne_zero n hmul.symm

/-- Multiplicities multiply along a tower `k ≤ m ≤ n`. -/
theorem uhfBlockDim_trans {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    uhfBlockDim m n * uhfBlockDim k m = uhfBlockDim k n := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k)
  rw [factorial_mul_uhfBlockDim (Nat.le_trans hkm hmn), Nat.mul_comm (uhfBlockDim m n),
    ← Nat.mul_assoc, factorial_mul_uhfBlockDim hkm, factorial_mul_uhfBlockDim hmn]

/-- The block coordinate `i / d` of an index of `M_{n!}`. -/
def uhfBlockProj {m n : ℕ} (h : m ≤ n) (i : Fin n.factorial) : Fin m.factorial :=
  ⟨i.1 / uhfBlockDim m n, (Nat.div_lt_iff_lt_mul (uhfBlockDim_pos h)).2 (by
    rw [factorial_mul_uhfBlockDim h]; exact i.isLt)⟩

/-- The multiplicity coordinate `i % d` of an index of `M_{n!}`. -/
def uhfBlockFiber {m n : ℕ} (h : m ≤ n) (i : Fin n.factorial) : Fin (uhfBlockDim m n) :=
  ⟨i.1 % uhfBlockDim m n, Nat.mod_lt _ (uhfBlockDim_pos h)⟩

/-- The index `p * d + r` of `M_{n!}` with block coordinate `p` and multiplicity
coordinate `r`. -/
def uhfBlockIndex {m n : ℕ} (h : m ≤ n) (p : Fin m.factorial) (r : Fin (uhfBlockDim m n)) :
    Fin n.factorial :=
  ⟨p.1 * uhfBlockDim m n + r.1, by
    calc p.1 * uhfBlockDim m n + r.1 < p.1 * uhfBlockDim m n + uhfBlockDim m n :=
          Nat.add_lt_add_left r.isLt _
      _ = (p.1 + 1) * uhfBlockDim m n := (Nat.add_one_mul _ _).symm
      _ ≤ m.factorial * uhfBlockDim m n := Nat.mul_le_mul_right _ p.isLt
      _ = n.factorial := factorial_mul_uhfBlockDim h⟩

theorem uhfBlockProj_index {m n : ℕ} (h : m ≤ n) (p : Fin m.factorial)
    (r : Fin (uhfBlockDim m n)) : uhfBlockProj h (uhfBlockIndex h p r) = p := by
  apply Fin.ext
  show (p.1 * uhfBlockDim m n + r.1) / uhfBlockDim m n = p.1
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (uhfBlockDim_pos h), Nat.div_eq_of_lt r.isLt,
    Nat.zero_add]

theorem uhfBlockFiber_index {m n : ℕ} (h : m ≤ n) (p : Fin m.factorial)
    (r : Fin (uhfBlockDim m n)) : uhfBlockFiber h (uhfBlockIndex h p r) = r := by
  apply Fin.ext
  show (p.1 * uhfBlockDim m n + r.1) % uhfBlockDim m n = r.1
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]

theorem uhfBlockIndex_proj_fiber {m n : ℕ} (h : m ≤ n) (i : Fin n.factorial) :
    uhfBlockIndex h (uhfBlockProj h i) (uhfBlockFiber h i) = i := by
  apply Fin.ext
  show i.1 / uhfBlockDim m n * uhfBlockDim m n + i.1 % uhfBlockDim m n = i.1
  exact Nat.div_add_mod' _ _

theorem uhfBlockIndex_eq_iff {m n : ℕ} (h : m ≤ n) (i : Fin n.factorial)
    (p : Fin m.factorial) (r : Fin (uhfBlockDim m n)) :
    i = uhfBlockIndex h p r ↔ uhfBlockProj h i = p ∧ uhfBlockFiber h i = r := by
  constructor
  · rintro rfl
    exact ⟨uhfBlockProj_index h p r, uhfBlockFiber_index h p r⟩
  · rintro ⟨hp, hr⟩
    rw [← hp, ← hr, uhfBlockIndex_proj_fiber]

theorem uhfBlockIndex_injective {m n : ℕ} (h : m ≤ n) {p q : Fin m.factorial}
    {r s : Fin (uhfBlockDim m n)} (hpq : uhfBlockIndex h p r = uhfBlockIndex h q s) :
    p = q ∧ r = s := by
  have h1 := uhfBlockProj_index h p r
  have h2 := uhfBlockFiber_index h p r
  rw [hpq, uhfBlockProj_index] at h1
  rw [hpq, uhfBlockFiber_index] at h2
  exact ⟨h1.symm, h2.symm⟩

/-- Block coordinates compose along a tower `k ≤ m ≤ n`. -/
theorem uhfBlockProj_proj {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (i : Fin n.factorial) :
    uhfBlockProj hkm (uhfBlockProj hmn i) = uhfBlockProj (Nat.le_trans hkm hmn) i := by
  apply Fin.ext
  show i.1 / uhfBlockDim m n / uhfBlockDim k m = i.1 / uhfBlockDim k n
  rw [Nat.div_div_eq_div_mul, uhfBlockDim_trans hkm hmn]

/-- Multiplicity coordinates along a tower `k ≤ m ≤ n`: two indices of `M_{n!}`
have the same `k`-multiplicity coordinate iff they have the same
`m`-multiplicity coordinate and their `m`-block coordinates have the same
`k`-multiplicity coordinate. -/
theorem uhfBlockFiber_eq_iff {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (i j : Fin n.factorial) :
    uhfBlockFiber (Nat.le_trans hkm hmn) i = uhfBlockFiber (Nat.le_trans hkm hmn) j ↔
      uhfBlockFiber hmn i = uhfBlockFiber hmn j ∧
        uhfBlockFiber hkm (uhfBlockProj hmn i) = uhfBlockFiber hkm (uhfBlockProj hmn j) := by
  simp only [Fin.ext_iff]
  show i.1 % uhfBlockDim k n = j.1 % uhfBlockDim k n ↔
      i.1 % uhfBlockDim m n = j.1 % uhfBlockDim m n ∧
        i.1 / uhfBlockDim m n % uhfBlockDim k m = j.1 / uhfBlockDim m n % uhfBlockDim k m
  rw [← uhfBlockDim_trans hkm hmn]
  constructor
  · intro hij
    constructor
    · rw [← Nat.mod_mul_right_mod i.1 (uhfBlockDim m n) (uhfBlockDim k m), hij,
        Nat.mod_mul_right_mod]
    · rw [← Nat.mod_mul_right_div_self i.1 (uhfBlockDim m n) (uhfBlockDim k m), hij,
        Nat.mod_mul_right_div_self]
  · rintro ⟨h1, h2⟩
    rw [Nat.mod_mul, Nat.mod_mul, h1, h2]

end GroupApproximation.Full.TWWSchafhauser
