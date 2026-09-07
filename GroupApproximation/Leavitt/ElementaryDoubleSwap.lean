import GroupApproximation.Leavitt.ElementaryWeylMonomial
import GroupApproximation.Leavitt.ElementaryNormalGeneration

/-!
# An involution normally generating the rank-four elementary group

Over every nontrivial unital ring, the positive permutation matrix of
`(01)(23)` is an involution in `EL₄`.  Its elementary word is
`w₀₁ w₂₃ w₀₂²`, not the square of a single Weyl element.  The latter
becomes the identity in characteristic two.

The two commutators printed in `non_mf_groups_exist.tex` extract
`e₀₃(-r)` from this involution.  Taking `r = -1` gives a unit root,
which normally generates the elementary group.
-/

namespace GroupApproximation.ElementaryDoubleSwap

open ElementaryWeyl

variable {R : Type*} [Ring R]

/-- The elementary word for the positive double transposition. -/
def doubleSwap : elementaryGroup (Fin 4) R :=
  weyl 0 1 (by decide) * weyl 2 3 (by decide) *
    (weyl 0 2 (by decide)) ^ 2

/-- The double transposition has no signs, in every characteristic. -/
theorem doubleSwap_val :
    ((doubleSwap (R := R) : (Matrix (Fin 4) (Fin 4) R)ˣ) :
        Matrix (Fin 4) (Fin 4) R) =
      Matrix.single 0 1 1 + Matrix.single 1 0 1 +
        Matrix.single 2 3 1 + Matrix.single 3 2 1 := by
  simp only [doubleSwap, Subgroup.coe_mul, weyl_val,
    pow_two, Units.val_mul, weylUnit_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply]

theorem doubleSwap_mul_self :
    doubleSwap (R := R) * doubleSwap = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, doubleSwap_val,
    Subgroup.coe_one, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.add_apply]

theorem doubleSwap_inv : (doubleSwap (R := R))⁻¹ = doubleSwap :=
  inv_eq_of_mul_eq_one_right doubleSwap_mul_self

theorem doubleSwap_ne_one [Nontrivial R] : doubleSwap (R := R) ≠ 1 := by
  intro h
  have h01 := congrArg
    (fun g : elementaryGroup (Fin 4) R ↦
      ((g : (Matrix (Fin 4) (Fin 4) R)ˣ) : Matrix (Fin 4) (Fin 4) R) 0 1) h
  simp [doubleSwap_val, Matrix.add_apply] at h01

theorem orderOf_doubleSwap [Nontrivial R] :
    orderOf (doubleSwap (R := R)) = 2 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 0) (x := doubleSwap (R := R))
    (by simpa using (doubleSwap_ne_one (R := R)))
    (by simpa [pow_two] using (doubleSwap_mul_self (R := R)))
  simpa using h

/-- Conjugating the first root by the positive double transposition. -/
theorem doubleSwap_conj_root (r : R) :
    doubleSwap * elGen (0 : Fin 4) 2 (by decide) r * doubleSwap⁻¹ =
      elGen (1 : Fin 4) 3 (by decide) r := by
  rw [doubleSwap_inv]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, doubleSwap_val]
  change _ * (1 + Matrix.single 0 2 r) * _ = 1 + Matrix.single 1 3 r
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single_apply,
      Matrix.one_apply, Matrix.add_apply]

/-- The first printed commutator, with zero-based indices. -/
theorem root_commutator_doubleSwap (r : R) :
    elGen (0 : Fin 4) 2 (by decide) r * doubleSwap *
        (elGen (0 : Fin 4) 2 (by decide) r)⁻¹ * doubleSwap⁻¹ =
      elGen (0 : Fin 4) 2 (by decide) r * elGen (1 : Fin 4) 3 (by decide) (-r) := by
  rw [← elGen_neg_eq_inv]
  simpa only [mul_assoc] using
    congrArg (fun g ↦ elGen (0 : Fin 4) 2 (by decide) r * g)
      (doubleSwap_conj_root (-r))

/-- The second printed commutator extracts `e₀₃(-r)`. -/
theorem root_commutator_pair (r : R) :
    elGen (0 : Fin 4) 1 (by decide) 1 *
        (elGen (0 : Fin 4) 2 (by decide) r * elGen (1 : Fin 4) 3 (by decide) (-r)) *
        (elGen (0 : Fin 4) 1 (by decide) 1)⁻¹ *
        (elGen (0 : Fin 4) 2 (by decide) r * elGen (1 : Fin 4) 3 (by decide) (-r))⁻¹ =
      elGen (0 : Fin 4) 3 (by decide) (-r) := by
  rw [mul_inv_rev]
  apply Subtype.ext
  apply Units.ext
  change (1 + Matrix.single 0 1 1) *
      ((1 + Matrix.single 0 2 r) * (1 + Matrix.single 1 3 (-r))) *
      (1 - Matrix.single 0 1 1) *
      ((1 - Matrix.single 1 3 (-r)) * (1 - Matrix.single 0 2 r)) =
    1 + Matrix.single 0 3 (-r)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.single_apply,
      Matrix.one_apply, Matrix.sub_apply, Matrix.add_apply]

/-- Every normal subgroup containing the double swap contains a unit root. -/
theorem root_mem_of_doubleSwap_mem
    (N : Subgroup (elementaryGroup (Fin 4) R)) [hN : N.Normal]
    (h : doubleSwap ∈ N) : elGen (0 : Fin 4) 3 (by decide) (1 : R) ∈ N := by
  have hpair : elGen (0 : Fin 4) 2 (by decide) (-1 : R) *
      elGen (1 : Fin 4) 3 (by decide) 1 ∈ N := by
    have hc := N.mul_mem
      (hN.conj_mem _ h (elGen (0 : Fin 4) 2 (by decide) (-1 : R))) (N.inv_mem h)
    simpa only [root_commutator_doubleSwap, neg_neg] using hc
  have hc := N.mul_mem
    (hN.conj_mem _ hpair (elGen (0 : Fin 4) 1 (by decide) (1 : R))) (N.inv_mem hpair)
  have heq := root_commutator_pair (-1 : R)
  simp only [neg_neg] at heq
  rw [heq] at hc
  exact hc

/-- The printed involution normally generates `EL₄` over every unital ring. -/
theorem normalClosure_doubleSwap_eq_top :
    Subgroup.normalClosure ({doubleSwap (R := R)} :
      Set (elementaryGroup (Fin 4) R)) = ⊤ := by
  let N := Subgroup.normalClosure ({doubleSwap (R := R)} :
    Set (elementaryGroup (Fin 4) R))
  haveI : N.Normal := Subgroup.normalClosure_normal
  exact elementaryGroup_normal_eq_top_of_elGen_mem (by simp) N (by decide)
    (root_mem_of_doubleSwap_mem N (Subgroup.subset_normalClosure rfl))
    ⟨1, 1, by simp⟩

end GroupApproximation.ElementaryDoubleSwap
