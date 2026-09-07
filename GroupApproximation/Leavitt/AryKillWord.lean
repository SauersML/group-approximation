import GroupApproximation.Leavitt.AryWords
import GroupApproximation.Meta.AxiomGuard

/-!
# The cylinder partition and the annihilating word, at arbitrary arity

Stage three of generalising

`LeavittWords → LeavittNormalForm → LeavittSimplicity → division`

from arity `2` to arity `d`.  This module carries the two pieces of
`Leavitt/LeavittSimplicity.lean` that I flagged as the real risk of the whole
programme, because unlike stages one and two they are not settled by reading
what a file consumes.

## The risk, and how it resolved

Stages one and two generalised because their binary files **consumed** only
facts that hold at any arity — two facts about the family, three about the
presentation.  That question can be answered by inspection.  `killWord` is
different in kind: it is a **construction**, `0^m 1`, built to disagree with its
own translates at a known position.  There is no "which facts does it use"
question to ask of a construction, so it had to be attempted.

**It generalises, and the reason is sharp: `killWord` needs the alphabet to have
*at least* two letters, not exactly two.**  The word `i₀^m i₁` works for any pair
of distinct indices, and the disagreement argument is unchanged — position `m`
holds `i₁` in the word itself and `i₀` in every short translate.  The single
place the binary file uses the exact arity is the final `by decide`, discharging
`(1 : Fin 2) ≠ 0`; here that becomes the hypothesis `i₁ ≠ i₀` and nothing else
moves.

So the construction was the right thing to worry about and the wrong thing to be
blocked by, which is only visible after doing it.

## Contents

* `sum_cylinder_ofFn` — the cylinders at a fixed depth partition unity.  This one
  *is* a consumption, and it consumes `F.complete` where the binary file
  consumed `sum_s_mul_t` through `Fin.sum_univ_two`.
* `eq_sum_mul_wordS_mul_wordT` — reconstruction of any element from its depth-`r`
  corners.
* `killWord`, `killWord_length`, `killWord_not_prefix` — the annihilating word
  and its defining property.

What remains of stage three is `exists_monomial_representation` and
`exists_mul_mul_eq_one`, roughly two hundred lines whose every step is prefix
combinatorics, `Finset` regrouping, or the words layer — all arity-independent,
and all now resting on generalised foundations.
-/

namespace GroupApproximation
namespace CompleteMatrixFamily

variable {A : Type*} [Ring A] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : CompleteMatrixFamily A ι)

/-! ### The cylinder partition of unity -/

/-- The cylinders at a fixed depth partition unity.

Where the binary file finishes with `Fin.sum_univ_two` and `sum_s_mul_t`, this
finishes with `F.complete` directly. -/
theorem sum_cylinder_ofFn (r : ℕ) :
    ∑ f : Fin r → ι, F.cylinder (List.ofFn f) = 1 := by
  induction r with
  | zero => simp [cylinder]
  | succ r ih =>
      have hsplit : ∀ (i : ι) (f : Fin r → ι),
          F.cylinder (List.ofFn (Fin.cons i f : Fin (r + 1) → ι))
            = F.left i * F.cylinder (List.ofFn f) * F.right i := by
        intro i f
        have hlist : List.ofFn (Fin.cons i f : Fin (r + 1) → ι)
            = i :: List.ofFn f := by
          simp [List.ofFn_succ]
        rw [hlist]
        unfold cylinder
        rw [wordS_cons, wordT_cons]
        simp only [mul_assoc]
      calc (∑ f : Fin (r + 1) → ι, F.cylinder (List.ofFn f))
          = ∑ p : ι × (Fin r → ι),
              F.cylinder (List.ofFn
                (Fin.cons p.1 p.2 : Fin (r + 1) → ι)) :=
            (Fintype.sum_equiv (Fin.consEquiv (fun _ ↦ ι))
              (fun p ↦ F.cylinder (List.ofFn
                (Fin.cons p.1 p.2 : Fin (r + 1) → ι)))
              (fun f ↦ F.cylinder (List.ofFn f))
              (fun _ ↦ rfl)).symm
        _ = ∑ i : ι, ∑ f : Fin r → ι,
              F.cylinder (List.ofFn
                (Fin.cons i f : Fin (r + 1) → ι)) :=
            Fintype.sum_prod_type _
        _ = ∑ i : ι, F.left i * F.right i := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            calc (∑ f : Fin r → ι, F.cylinder
                  (List.ofFn (Fin.cons i f : Fin (r + 1) → ι)))
                = F.left i *
                    (∑ f : Fin r → ι, F.cylinder (List.ofFn f)) *
                      F.right i := by
                  rw [Finset.mul_sum, Finset.sum_mul]
                  exact Finset.sum_congr rfl fun f _ ↦ hsplit i f
              _ = F.left i * F.right i := by rw [ih, mul_one]
        _ = 1 := F.complete

/-- Reconstruction of any element from its depth-`r` corners. -/
theorem eq_sum_mul_wordS_mul_wordT (x : A) (r : ℕ) :
    x = ∑ f : Fin r → ι,
      x * F.wordS (List.ofFn f) * F.wordT (List.ofFn f) := by
  calc x = x * ∑ f : Fin r → ι, F.cylinder (List.ofFn f) := by
        rw [sum_cylinder_ofFn, mul_one]
    _ = ∑ f : Fin r → ι,
          x * F.wordS (List.ofFn f) * F.wordT (List.ofFn f) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ ↦ ?_
        unfold cylinder
        rw [mul_assoc]

end CompleteMatrixFamily

/-! ### The annihilating word

This section is pure list combinatorics: no ring, no family, only a type with
two distinguished distinct elements. -/

namespace AryKillWord

variable {ι : Type*}

/-- The aperiodic annihilating word `i₀^m i₁`.

The binary file writes `0^m 1`.  All the argument needs is that the two letters
**differ**, not that there are exactly two of them. -/
def killWord (i₀ i₁ : ι) (m : ℕ) : List ι := List.replicate m i₀ ++ [i₁]

@[simp] theorem killWord_length (i₀ i₁ : ι) (m : ℕ) :
    (killWord i₀ i₁ m).length = m + 1 := by
  simp [killWord]

/-- `i₀^m i₁` is not a prefix of `ε ++ i₀^m i₁` for `1 ≤ |ε| ≤ m`: the two words
disagree at position `m`, which holds `i₁` on the left and `i₀` on the right.

The binary version discharges the final disagreement with `by decide` on
`Fin 2`; here it is the hypothesis `i₁ ≠ i₀`, and that substitution is the whole
generalisation. -/
theorem killWord_not_prefix (i₀ i₁ : ι) (hne : i₁ ≠ i₀) (ε : List ι) (m : ℕ)
    (hεne : ε ≠ []) (hlen : ε.length ≤ m) :
    ¬ (killWord i₀ i₁ m <+: ε ++ killWord i₀ i₁ m) := by
  intro hpre
  have hεpos : 0 < ε.length := List.length_pos_iff.mpr hεne
  have hklen : (killWord i₀ i₁ m).length = m + 1 := killWord_length i₀ i₁ m
  have hm1 : m < (killWord i₀ i₁ m).length := by omega
  have hm2 : m < (ε ++ killWord i₀ i₁ m).length := by
    rw [List.length_append]
    omega
  have hagree : (killWord i₀ i₁ m)[m]'hm1
      = (ε ++ killWord i₀ i₁ m)[m]'hm2 := hpre.getElem hm1
  have hlast : (killWord i₀ i₁ m)[m]'hm1 = i₁ := by
    unfold killWord
    rw [List.getElem_append_right (by simp)]
    simp
  have hmid : (ε ++ killWord i₀ i₁ m)[m]'hm2 = i₀ := by
    rw [List.getElem_append_right (by omega)]
    unfold killWord
    rw [List.getElem_append_left (by
      rw [List.length_replicate]
      omega)]
    simp
  rw [hlast, hmid] at hagree
  exact hne hagree

end AryKillWord

end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.CompleteMatrixFamily.sum_cylinder_ofFn
#audit_axioms GroupApproximation.CompleteMatrixFamily.eq_sum_mul_wordS_mul_wordT
#audit_axioms GroupApproximation.AryKillWord.killWord_not_prefix
