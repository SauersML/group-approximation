import GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion
import GroupApproximation.Leavitt.ElementaryWeylMonomial
import GroupApproximation.Meta.AxiomGuard

/-!
# Introduction: every example has torsion, in every characteristic

`non_mf_groups_exist.tex`, tex 292–293 (census row `80279f06992b`):

> Every example above has torsion, and in the lamp construction the obstruction is itself a torsion element.

`IntroExamplesTorsion.PrintedIntroExamplesTorsion` carries `EL_n(R)` only over rings with `p · 1 = 0`, `p > 0`.
The examples above also include `EL_n(R)` in characteristic zero: `EL_n(R)` over every countable unital ring with
`ts = 1` and full `1 - st` (tex 221–223), and `EL_4(𝒞)` with `𝒞 = ℤ⟨s_0, s_1, t_0, t_1⟩/(t_i s_j - δ_ij)`
(tex 215–219).  Over every nonzero ring `R` and every `n ≥ 2`, the Weyl element
`w = e₁₂(1) e₂₁(-1) e₁₂(1) ∈ EL_n(R)` satisfies `w² = 1 - 2(E₁₁ + E₂₂)`, so `w⁴ = 1`, while `w ≠ 1`, because
its `(1,1)` entry is `0`.

* `weylUnit_mul_self`: `w² = 1 - 2 E_uu - 2 E_vv`.
* `weylUnit_pow_four`: `w⁴ = 1`.
* `exists_elementary_torsion_of_nontrivial`: `EL_n(R)`, `n ≥ 2`, has a nontrivial element of finite order over
  every nonzero ring.
* `PrintedIntroExamplesTorsionAllCharacteristics`, `printedIntroExamplesTorsionAllCharacteristics`: the printed
  sentence with the elementary examples in every characteristic, with nothing assumed.
-/

namespace GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion

open ElementaryWeyl

variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Ring S]

/-- **`w² = 1 - 2E_uu - 2E_vv`** for the Weyl element `w = e_uv(1) e_vu(-1) e_uv(1)`. -/
theorem weylUnit_mul_self (u v : ι) (huv : u ≠ v) :
    (weylUnit (S := S) u v huv : Matrix ι ι S) * weylUnit (S := S) u v huv =
      1 - 2 * Matrix.single u u (1 : S) - 2 * Matrix.single v v (1 : S) := by
  nth_rewrite 2 [weylUnit_val]
  simp only [mul_add, mul_sub, mul_one, weylUnit_val_mul_single_fst, weylUnit_val_mul_single_snd]
  rw [weylUnit_val]
  noncomm_ring

/-- **`w⁴ = 1`.** -/
theorem weylUnit_pow_four (u v : ι) (huv : u ≠ v) : weylUnit (S := S) u v huv ^ 4 = 1 := by
  have huu : Matrix.single u u (1 : S) * Matrix.single u u (1 : S) = Matrix.single u u 1 := by
    rw [Matrix.single_mul_single_same, one_mul]
  have hvv : Matrix.single v v (1 : S) * Matrix.single v v (1 : S) = Matrix.single v v 1 := by
    rw [Matrix.single_mul_single_same, one_mul]
  have huv' : Matrix.single u u (1 : S) * Matrix.single v v (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) u u v huv 1
  have hvu : Matrix.single v v (1 : S) * Matrix.single u u (1 : S) = 0 :=
    Matrix.single_mul_single_of_ne (c := (1 : S)) v v u huv.symm 1
  have hw2 : (weylUnit (S := S) u v huv : Matrix ι ι S) * weylUnit (S := S) u v huv =
      1 - 2 * (Matrix.single u u (1 : S) + Matrix.single v v (1 : S)) := by
    rw [weylUnit_mul_self]
    noncomm_ring
  have hP : (Matrix.single u u (1 : S) + Matrix.single v v (1 : S)) *
      (Matrix.single u u (1 : S) + Matrix.single v v (1 : S)) =
        Matrix.single u u (1 : S) + Matrix.single v v (1 : S) := by
    rw [add_mul, mul_add, mul_add, huu, hvv, huv', hvu, add_zero, zero_add]
  have hsq : ∀ P : Matrix ι ι S, (1 - 2 * P) * (1 - 2 * P) = 1 - 4 * P + 4 * (P * P) := fun P => by
    noncomm_ring
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one, show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hw2, hsq, hP]
  noncomm_ring

/-- The Weyl element lies in `EL_n`: it is a product of three elementary units. -/
theorem weylUnit_mem_elementaryGroup (u v : ι) (huv : u ≠ v) :
    weylUnit (S := S) u v huv ∈ elementaryGroup ι S :=
  (elementaryGroup ι S).mul_mem
    ((elementaryGroup ι S).mul_mem (elementaryUnit_mem u v huv 1) (elementaryUnit_mem v u huv.symm (-1)))
    (elementaryUnit_mem u v huv 1)

/-- **`w ≠ 1`** over a nonzero ring: `w E_uu = -E_vu`, whose `(u,u)` entry is `0`, not `1`. -/
theorem weylUnit_ne_one [Nontrivial S] (u v : ι) (huv : u ≠ v) : weylUnit (S := S) u v huv ≠ 1 := by
  intro hw
  have hm := weylUnit_val_mul_single_fst (S := S) u v huv u (1 : S)
  rw [hw, Units.val_one, one_mul] at hm
  have he : (Matrix.single u u (1 : S)) u u = (-Matrix.single v u (1 : S)) u u :=
    congrArg (fun M : Matrix ι ι S => M u u) hm
  rw [Matrix.single_apply_same, Matrix.neg_apply, Matrix.single_apply_of_row_ne huv.symm u u (1 : S),
    neg_zero] at he
  exact one_ne_zero he

/-- The Weyl element has finite order. -/
theorem isOfFinOrder_weylUnit (u v : ι) (huv : u ≠ v) : IsOfFinOrder (weylUnit (S := S) u v huv) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨4, by norm_num, weylUnit_pow_four u v huv⟩

/-- **Torsion in `EL_n(R)` over every nonzero ring**, `n ≥ 2`: the Weyl element. -/
theorem exists_elementary_torsion_of_nontrivial (R : Type*) [Ring R] [Nontrivial R] (n : ℕ) (hn : 2 ≤ n) :
    ∃ g ∈ elementaryGroup (Fin n) R, g ≠ 1 ∧ IsOfFinOrder g := by
  have h0 : 0 < n := by omega
  have h1 : 1 < n := by omega
  have hne : (⟨0, h0⟩ : Fin n) ≠ ⟨1, h1⟩ := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  exact ⟨weylUnit (S := R) ⟨0, h0⟩ ⟨1, h1⟩ hne, weylUnit_mem_elementaryGroup _ _ hne,
    weylUnit_ne_one _ _ hne, isOfFinOrder_weylUnit _ _ hne⟩

/-- **"Every example above has torsion, and in the lamp construction the obstruction is itself a torsion
element"** (tex 292–293), with the elementary examples in every characteristic. -/
def PrintedIntroExamplesTorsionAllCharacteristics : Prop :=
  PrintedIntroExamplesTorsion ∧
    ∀ (R : Type) [Ring R] [Nontrivial R] (n : ℕ), 2 ≤ n →
      ∃ g ∈ elementaryGroup (Fin n) R, g ≠ 1 ∧ IsOfFinOrder g

theorem printedIntroExamplesTorsionAllCharacteristics : PrintedIntroExamplesTorsionAllCharacteristics :=
  ⟨manuscriptIntroExamplesTorsion, fun R _ _ n hn => exists_elementary_torsion_of_nontrivial R n hn⟩

end GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion

#audit_axioms GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.weylUnit_pow_four
#audit_closed_axioms
  GroupApproximation.Manuscript.NonMFSentences.IntroExamplesTorsion.printedIntroExamplesTorsionAllCharacteristics
