import GroupApproximation.Leavitt.PrefixCode
import GroupApproximation.Meta.AxiomGuard

/-!
# Frame cone: leaf permutations and the left-comb leaves of rank four

Khanh (arXiv:2609.08428), proof of Prop. `prop:frame-cone`:

> Fix `Φ = L_r^* : R → R^r`. … put `v = Φx`, `y_i = ρ_i v = a_i x`, `b_i = η_i^*`.

Here `Φ` is the left-comb self-similarity `A ≅ A^4` with leaves `d_j = s_{1^j0}` (`j < 3`),
`d_3 = s_{111}`. This file provides

* `permUnit F π`: for a complete matrix family `F` and `π : Perm ι`, the unit
  `Σ_i left (π i) · right i`, with `permUnit F π · left j = left (π j)`;
* comb facts: for `j < k`, `t_{1^k} · d_j = 0`, and for `k < 3`, `d_k = s_{1^k} s_0`.

Lane LVFrame (leaf T1c of the `K₂(4, L) = ⊥` tree, `simple_kazhdan_sofic_group.tex` l.733-735):
port of the foreign module `LeavittK2/FrameCone/Comb.lean`, whose closure contains WIP commits.
-/

namespace GroupApproximation.Full.LVFrame

section Perm

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-- The leaf permutation element `Σ_i left (π i) · right i`. -/
def permElt (π : Equiv.Perm ι) : A := ∑ i, F.left (π i) * F.right i

#audit_axioms GroupApproximation.Full.LVFrame.permElt

theorem permElt_mul_left (π : Equiv.Perm ι) (j : ι) :
    permElt F π * F.left j = F.left (π j) := by
  simp [permElt, Finset.sum_mul, mul_assoc, F.orthogonal]

#audit_axioms GroupApproximation.Full.LVFrame.permElt_mul_left

theorem permElt_mul_symm (π : Equiv.Perm ι) : permElt F π * permElt F π.symm = 1 := by
  calc
    permElt F π * permElt F π.symm =
        ∑ i, permElt F π * F.left (π.symm i) * F.right i := by
      rw [show permElt F π.symm = ∑ i, F.left (π.symm i) * F.right i from rfl, Finset.mul_sum]
      simp only [mul_assoc]
    _ = ∑ i, F.left i * F.right i := by
      simp only [permElt_mul_left, Equiv.apply_symm_apply]
    _ = 1 := F.complete

#audit_axioms GroupApproximation.Full.LVFrame.permElt_mul_symm

theorem permElt_symm_mul (π : Equiv.Perm ι) : permElt F π.symm * permElt F π = 1 := by
  have h := permElt_mul_symm F π.symm
  rwa [Equiv.symm_symm] at h

#audit_axioms GroupApproximation.Full.LVFrame.permElt_symm_mul

/-- The leaf permutation unit. -/
def permUnit (π : Equiv.Perm ι) : Aˣ :=
  ⟨permElt F π, permElt F π.symm, permElt_mul_symm F π, permElt_symm_mul F π⟩

#audit_axioms GroupApproximation.Full.LVFrame.permUnit

theorem permUnit_mul_left (π : Equiv.Perm ι) (j : ι) :
    (permUnit F π : A) * F.left j = F.left (π j) :=
  permElt_mul_left F π j

#audit_axioms GroupApproximation.Full.LVFrame.permUnit_mul_left

end Perm

section Comb

variable {A : Type*} [Ring A] (L : LeavittFamily A)

theorem leftCombWord_three_of_lt (j : Fin 4) (hj : j.val < 3) :
    leftCombWord 3 j = List.replicate j.val 1 ++ [0] := by
  simp [leftCombWord, hj]

#audit_axioms GroupApproximation.Full.LVFrame.leftCombWord_three_of_lt

/-- `t_{1^k} s_{1^j 0} = 0` for `j < k`. -/
theorem comb_orth (j k : ℕ) (hjk : j < k) :
    L.wordT (List.replicate k 1) * L.wordS (List.replicate j 1 ++ [0]) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = j + (m + 1) := ⟨k - j - 1, by omega⟩
  rw [← List.replicate_append_replicate, L.wordT_append,
    mul_assoc (L.wordT (List.replicate (m + 1) 1)), L.wordT_mul_wordS_append_left,
    List.replicate_succ, LeavittFamily.wordT_cons, LeavittFamily.wordS_cons,
    LeavittFamily.wordS_nil, LeavittFamily.t_one, LeavittFamily.s_zero, mul_one, mul_assoc,
    L.t1_s0, mul_zero]

#audit_axioms GroupApproximation.Full.LVFrame.comb_orth

/-- `ρ = t_{1^k}` kills the comb leaves `d_j`, `j < k ≤ 2`. -/
theorem comb_rho_left (k : ℕ) (hk : k ≤ 2) (j : Fin 4) (hj : j.val < k) :
    L.wordT (List.replicate k 1) * L.wordS (leftCombWord 3 j) = 0 := by
  rw [leftCombWord_three_of_lt j (by omega)]
  exact comb_orth L j.val k hj

#audit_axioms GroupApproximation.Full.LVFrame.comb_rho_left

/-- `d_k = σ s_0` with `σ = s_{1^k}`, `k ≤ 2`. -/
theorem comb_left_self (k : ℕ) (hk : k ≤ 2) :
    L.wordS (leftCombWord 3 ⟨k, by omega⟩) = L.wordS (List.replicate k 1) * L.s0 := by
  rw [leftCombWord_three_of_lt ⟨k, by omega⟩ (show k < 3 by omega), L.wordS_append,
    LeavittFamily.wordS_cons, LeavittFamily.wordS_nil, LeavittFamily.s_zero, mul_one]

#audit_axioms GroupApproximation.Full.LVFrame.comb_left_self

end Comb

end GroupApproximation.Full.LVFrame
