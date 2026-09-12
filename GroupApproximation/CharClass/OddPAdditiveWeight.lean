import GroupApproximation.CharClass.OddPTupleAction
import GroupApproximation.Meta.AxiomGuard
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Redistributing a sum over mixed assignments along the rotation orbits

The additivity of the odd-primary reduced powers expands `(u + v)^{⊗p}` into a sum over assignments
`ε : Fin p → Bool` (which slots carry `u`), and has to show that the **mixed** part — `ε` neither
constantly `true` nor constantly `false` — is a coboundary.  The classical argument groups the mixed
assignments into orbits of the cyclic rotation, which are free because `p` is prime, and sums each
orbit into the norm element.  Choosing orbit representatives is expensive to formalise, so this file
replaces it by a **weight**.

For a mixed `ε`, `c(ε) := #{l | ε l}` lies strictly between `0` and `p`, so it is a unit mod `p`, and

    w(ε) := c(ε)⁻¹  if ε 0 = true,   0  otherwise

sums to one along every rotation orbit: `ε ∘ (finRotate p)^i` sends slot `0` to slot `i`, so the
`i ∈ range p` with `ε (i) = true` are exactly the slots `ε` marks, `c(ε)` of them.  Hence for any `F`

    ∑_{ε} w(ε) • ∑_{i<p} F (ε ∘ ((finRotate p).symm)^i) = ∑_{ε mixed} F ε ,

which is the orbit sum with no representative chosen (`sum_weighted_rotate_eq_mixed`).  The weight
of a non-mixed assignment is `0` along its whole orbit, so no filter appears in the statement.
-/

namespace GroupApproximation.CharClass

noncomputable section

variable (p : ℕ) [NeZero p]

/-! ## 1. The count and the weight -/

/-- The number of slots an assignment marks, in `ZMod p`. -/
def trueCount (ε : Fin p → Bool) : ZMod p := ∑ l, if ε l = true then (1 : ZMod p) else 0

/-- **The orbit weight**: the inverse count when slot `0` is marked and some slot is not, else `0`. -/
def mixedWeight (ε : Fin p → Bool) : ZMod p :=
  if (∃ l, ε l = false) ∧ ε 0 = true then (trueCount p ε)⁻¹ else 0

omit [NeZero p] in
/-- Permuting the slots does not change the count. -/
theorem trueCount_comp (ε : Fin p → Bool) (π : Equiv.Perm (Fin p)) :
    trueCount p (fun l => ε (π l)) = trueCount p ε := by
  unfold trueCount
  exact Equiv.sum_comp π (fun l => if ε l = true then (1 : ZMod p) else 0)

omit [NeZero p] in
/-- **The count of a mixed assignment is a unit mod `p`.** -/
theorem trueCount_ne_zero [Fact p.Prime] (ε : Fin p → Bool) (ht : ∃ l, ε l = true)
    (hf : ∃ l, ε l = false) : trueCount p ε ≠ 0 := by
  intro h0
  have hcard : trueCount p ε = ((Finset.univ.filter fun l => ε l = true).card : ZMod p) := by
    unfold trueCount
    rw [Finset.natCast_card_filter]
  rw [hcard, CharP.cast_eq_zero_iff (ZMod p) p] at h0
  have hpos : 0 < (Finset.univ.filter fun l => ε l = true).card := by
    obtain ⟨l, hl⟩ := ht
    exact Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩⟩
  have hlt : (Finset.univ.filter fun l => ε l = true).card < p := by
    obtain ⟨l, hl⟩ := hf
    have hss : (Finset.univ.filter fun l => ε l = true) ⊂ Finset.univ :=
      Finset.filter_ssubset.mpr ⟨l, Finset.mem_univ l, by simp [hl]⟩
    have h := Finset.card_lt_card hss
    rwa [Finset.card_univ, Fintype.card_fin] at h
  exact absurd (Nat.le_of_dvd hpos h0) (not_le.mpr hlt)

/-! ## 2. The orbit of slot `0` -/

/-- `(finRotate p)^i` carries slot `0` to slot `i`. -/
theorem finRotate_pow_apply_zero (i : ℕ) (hi : i < p) :
    ((finRotate p) ^ i) 0 = ⟨i, hi⟩ := by
  induction i with
  | zero => exact Fin.ext (by simp)
  | succ i ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    exact Fin.ext ((finRotate_val_eq _).trans (Nat.mod_eq_of_lt hi))

/-- **The weight sums to one along the orbit of a mixed assignment.** -/
theorem sum_mixedWeight_rotate [Fact p.Prime] (ε : Fin p → Bool) (ht : ∃ l, ε l = true)
    (hf : ∃ l, ε l = false) :
    ∑ i ∈ Finset.range p, mixedWeight p (fun l => ε (((finRotate p) ^ i) l)) = 1 := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => mixedWeight p (fun l => ε (((finRotate p) ^ i) l))) p]
  have hterm : ∀ i : Fin p, mixedWeight p (fun l => ε (((finRotate p) ^ (i : ℕ)) l))
      = if ε i = true then (trueCount p ε)⁻¹ else 0 := by
    intro i
    have hz : ((finRotate p) ^ (i : ℕ)) 0 = i := finRotate_pow_apply_zero p i i.2
    have hcount : trueCount p (fun l => ε (((finRotate p) ^ (i : ℕ)) l)) = trueCount p ε :=
      trueCount_comp p ε _
    have hfalse : ∃ l, ε (((finRotate p) ^ (i : ℕ)) l) = false := by
      obtain ⟨l, hl⟩ := hf
      exact ⟨((finRotate p) ^ (i : ℕ)).symm l, by rw [Equiv.apply_symm_apply]; exact hl⟩
    unfold mixedWeight
    simp only [hz, hcount, hfalse, true_and]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  have hmul : ∑ i : Fin p, (if ε i = true then (trueCount p ε)⁻¹ else 0)
      = (trueCount p ε)⁻¹ * ∑ i : Fin p, (if ε i = true then (1 : ZMod p) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [hmul]
  exact inv_mul_cancel₀ (trueCount_ne_zero p ε ht hf)

/-- Along the orbit of an assignment that is not mixed, the weight vanishes identically. -/
theorem sum_mixedWeight_rotate_ite [Fact p.Prime] (ε : Fin p → Bool) :
    ∑ i ∈ Finset.range p, mixedWeight p (fun l => ε (((finRotate p) ^ i) l))
      = if (∃ l, ε l = true) ∧ (∃ l, ε l = false) then 1 else 0 := by
  split_ifs with h
  · exact sum_mixedWeight_rotate p ε h.1 h.2
  · refine Finset.sum_eq_zero fun i _ => ?_
    unfold mixedWeight
    rw [if_neg]
    rintro ⟨⟨l, hl⟩, h0⟩
    exact h ⟨⟨_, h0⟩, ⟨_, hl⟩⟩

/-! ## 3. The redistribution -/

omit [NeZero p] in
/-- `((finRotate p).symm)^i` inverts `(finRotate p)^i`. -/
theorem finRotate_symm_pow_apply_pow (i : ℕ) (l : Fin p) :
    ((finRotate p).symm ^ i) (((finRotate p) ^ i) l) = l := by
  rw [← Equiv.Perm.inv_def, inv_pow, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

omit [NeZero p] in
theorem finRotate_pow_apply_symm_pow (i : ℕ) (l : Fin p) :
    ((finRotate p) ^ i) (((finRotate p).symm ^ i) l) = l := by
  rw [← Equiv.Perm.inv_def, inv_pow, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

/-- **The orbit sum with no representative chosen.** -/
theorem sum_weighted_rotate_eq_mixed [Fact p.Prime] {M : Type*} [AddCommGroup M]
    [Module (ZMod p) M] (F : (Fin p → Bool) → M) :
    ∑ ε : Fin p → Bool,
        mixedWeight p ε • ∑ i ∈ Finset.range p, F (fun l => ε (((finRotate p).symm ^ i) l))
      = ∑ ε : Fin p → Bool, if (∃ l, ε l = true) ∧ (∃ l, ε l = false) then F ε else 0 := by
  have hre : ∀ i ∈ Finset.range p,
      ∑ ε : Fin p → Bool, mixedWeight p ε • F (fun l => ε (((finRotate p).symm ^ i) l))
        = ∑ ε : Fin p → Bool, mixedWeight p (fun l => ε (((finRotate p) ^ i) l)) • F ε := by
    intro i _
    refine Finset.sum_nbij' (fun ε l => ε (((finRotate p).symm ^ i) l))
      (fun ε l => ε (((finRotate p) ^ i) l))
      (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
      (fun ε _ => funext fun l => by
        show ε (((finRotate p).symm ^ i) (((finRotate p) ^ i) l)) = ε l
        rw [finRotate_symm_pow_apply_pow])
      (fun ε _ => funext fun l => by
        show ε (((finRotate p) ^ i) (((finRotate p).symm ^ i) l)) = ε l
        rw [finRotate_pow_apply_symm_pow])
      (fun ε _ => ?_)
    simp only [finRotate_symm_pow_apply_pow]
  calc ∑ ε : Fin p → Bool,
        mixedWeight p ε • ∑ i ∈ Finset.range p, F (fun l => ε (((finRotate p).symm ^ i) l))
      = ∑ i ∈ Finset.range p,
          ∑ ε : Fin p → Bool, mixedWeight p ε • F (fun l => ε (((finRotate p).symm ^ i) l)) := by
        simp only [Finset.smul_sum]
        exact Finset.sum_comm
    _ = ∑ i ∈ Finset.range p,
          ∑ ε : Fin p → Bool, mixedWeight p (fun l => ε (((finRotate p) ^ i) l)) • F ε :=
        Finset.sum_congr rfl hre
    _ = ∑ ε : Fin p → Bool,
          ∑ i ∈ Finset.range p, mixedWeight p (fun l => ε (((finRotate p) ^ i) l)) • F ε :=
        Finset.sum_comm
    _ = ∑ ε : Fin p → Bool, if (∃ l, ε l = true) ∧ (∃ l, ε l = false) then F ε else 0 := by
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [← Finset.sum_smul, sum_mixedWeight_rotate_ite]
        split_ifs <;> simp

/-- **Splitting off the two constant assignments.** -/
theorem sum_eq_mixed_add_const {M : Type*} [AddCommGroup M] (F : (Fin p → Bool) → M) :
    ∑ ε : Fin p → Bool, F ε
      = (∑ ε : Fin p → Bool, if (∃ l, ε l = true) ∧ (∃ l, ε l = false) then F ε else 0)
        + F (fun _ => true) + F (fun _ => false) := by
  have hpt : ∀ ε : Fin p → Bool,
      F ε = (if (∃ l, ε l = true) ∧ (∃ l, ε l = false) then F ε else 0)
        + (if ε = (fun _ => true) then F ε else 0) + (if ε = (fun _ => false) then F ε else 0) := by
    intro ε
    by_cases ht : ∃ l, ε l = true
    · by_cases hf : ∃ l, ε l = false
      · obtain ⟨l₁, hl₁⟩ := ht
        obtain ⟨l₂, hl₂⟩ := hf
        have h1 : ε ≠ (fun _ => true) := fun h => by
          have h' := congrFun h l₂
          rw [hl₂] at h'
          exact Bool.false_ne_true h'
        have h2 : ε ≠ (fun _ => false) := fun h => by
          have h' := congrFun h l₁
          rw [hl₁] at h'
          exact Bool.false_ne_true h'.symm
        rw [if_pos ⟨⟨l₁, hl₁⟩, ⟨l₂, hl₂⟩⟩, if_neg h1, if_neg h2, add_zero, add_zero]
      · have h1 : ε = (fun _ => true) := funext fun l => by
          cases hε : ε l
          · exact (hf ⟨l, hε⟩).elim
          · rfl
        have h2 : ε ≠ (fun _ => false) := fun h => by
          have h' := congrFun (h1.symm.trans h) 0
          exact Bool.false_ne_true h'.symm
        rw [if_neg (fun h => hf h.2), if_pos h1, if_neg h2, zero_add, add_zero]
    · have h2 : ε = (fun _ => false) := funext fun l => by
        cases hε : ε l
        · rfl
        · exact (ht ⟨l, hε⟩).elim
      have h1 : ε ≠ (fun _ => true) := fun h => by
        have h' := congrFun (h2.symm.trans h) 0
        exact Bool.false_ne_true h'
      rw [if_neg (fun h => ht h.1), if_neg h1, if_pos h2, zero_add, zero_add]
  refine (Finset.sum_congr rfl fun ε _ => hpt ε).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]

#audit_axioms trueCount_ne_zero
#audit_axioms sum_mixedWeight_rotate
#audit_axioms sum_weighted_rotate_eq_mixed
#audit_axioms sum_eq_mixed_add_const

end

end GroupApproximation.CharClass
