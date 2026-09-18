import GroupApproximation.Leavitt.PreusserNormalizedBy
import GroupApproximation.Pestov91.SimpleModCentre
import GroupApproximation.Meta.AxiomGuard

/-!
# Stepanov's Theorem 4.4 over a simple ring, part 1: subgroups without transvections

`simple_kazhdan_sofic_group.tex`, the remark after `sec:proof`'s subsection "Simplicity"
(tex l.307–315): "simplicity also follows from Stepanov's theorem on the normal structure of
$\GL_n$ [Stepanov, Theorem 4.4]".

Stepanov, *On the normal structure of the general linear group over a ring*, J. Math. Sci. 95
(1999), Theorem 4.4 (pp. 2151–2152).  Over a simple ring the only proper ideal is `0`, condition
(a) is vacuous and (b) is `StepanovConditionB` (in `NormalStructure`).  This file proves the
unit-column form of Lemma 4.1 used on p. 2152, for a subgroup `H` normalized by `E(ι, R)` that
contains no nontrivial transvection:

* `colMatrix_eq_zero_of_mem`: a column transvection in `H` is trivial;
* `eq_one_of_row_eq_one`: an element of `H` whose row `j` is the unit row is trivial;
* `mem_congruenceSubgroup_bot_of_entry_eq_zero`: a zero off-diagonal entry makes the element central.

Adapted (lane-owned copy, namespace `GroupApproximation.Full.StepanovMatui`) from the never-wired
orphan `GroupApproximation/Algebra/StepanovNormalStructure.lean`.
-/

namespace GroupApproximation
namespace Full
namespace StepanovMatui

open scoped commutatorElement Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-! ### Matrix identities -/

theorem colMatrix_mul_apply (q : ι) (y : ι → R) (N : Matrix ι ι R) (a b : ι) :
    (ElementarySimplicity.colMatrix q y * N) a b = y a * N q b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · rw [ElementarySimplicity.colMatrix_apply, if_pos rfl]
  · intro c _ hc
    rw [ElementarySimplicity.colMatrix_apply, if_neg hc, zero_mul]
  · intro hq
    exact absurd (Finset.mem_univ q) hq

/-- A left factor whose row `j` is the unit row leaves row `j` of the product unchanged. -/
theorem mul_apply_of_row_eq_one {M N : Matrix ι ι R} {j : ι}
    (h : ∀ b, M j b = (1 : Matrix ι ι R) j b) (b : ι) : (M * N) j b = N j b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [h j, Matrix.one_apply_eq, one_mul]
  · intro c _ hc
    rw [h c, Matrix.one_apply_ne (Ne.symm hc), zero_mul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem colDefect_eq_colMatrix {i : ι} {y : ι → R} (hyi : y i = 0) :
    RowAnnihilator.colDefect i y = ElementarySimplicity.colMatrix i y := by
  ext p q
  rw [RowAnnihilator.colDefect_apply, ElementarySimplicity.colMatrix_apply]
  by_cases hq : q = i
  · rw [if_pos hq, if_pos hq]
    by_cases hp : p = i
    · rw [if_pos hp, hp, hyi]
    · rw [if_neg hp]
  · rw [if_neg hq, if_neg hq]

/-- The commutator of two square-zero perturbations of `1`. -/
theorem one_add_mul_one_add_mul_one_sub_mul_one_sub {A : Type*} [Ring A] (W S : A)
    (hWW : W * W = 0) (hWS : W * S = 0) (hSS : S * S = 0) (hSWS : S * W * S = 0) :
    (1 + W) * (1 + S) * (1 - W) * (1 - S) = 1 - S * W := by
  have e : (1 + W) * (1 + S) * (1 - W) * (1 - S) =
      1 + W * S - S * W - W * W - W * S * W - S * S - W * S * S + S * W * S + W * W * S +
        W * S * W * S := by
    noncomm_ring
  rw [e, hWS, hWW, hSS, hSWS]
  simp only [zero_mul, add_zero, sub_zero]

theorem one_add_colMatrix_mul_one_sub_single (j l : ι) (hlj : l ≠ j) (y : ι → R) :
    (1 + ElementarySimplicity.colMatrix j y) * (1 - Matrix.single l j (1 : R)) =
      1 + ElementarySimplicity.colMatrix j (fun a => y a - (1 : Matrix ι ι R) a l) := by
  have hVS : ElementarySimplicity.colMatrix j y * Matrix.single l j (1 : R) = 0 :=
    ElementarySimplicity.colMatrix_mul_single_of_ne j y l j 1 hlj
  have e : (1 + ElementarySimplicity.colMatrix j y) * (1 - Matrix.single l j (1 : R)) =
      1 + (ElementarySimplicity.colMatrix j y - Matrix.single l j (1 : R)) -
        ElementarySimplicity.colMatrix j y * Matrix.single l j (1 : R) := by
    noncomm_ring
  rw [e, hVS, sub_zero]
  clear e hVS
  congr 1
  ext a b
  rw [Matrix.sub_apply, ElementarySimplicity.colMatrix_apply, ElementarySimplicity.colMatrix_apply,
    Matrix.single_apply]
  by_cases hb : b = j
  · rw [if_pos hb, if_pos hb]
    by_cases ha : a = l
    · rw [if_pos (show l = a ∧ j = b from ⟨ha.symm, hb.symm⟩), ha, Matrix.one_apply_eq]
    · rw [if_neg (show ¬(l = a ∧ j = b) from fun h => ha h.1.symm), Matrix.one_apply_ne ha]
  · rw [if_neg hb, if_neg hb, if_neg (show ¬(l = a ∧ j = b) from fun h => hb h.2.symm), sub_zero]

/-! ### Subgroups without nontrivial transvections -/

/-- `H` contains no nontrivial elementary transvection. -/
def NoTransvection (H : Subgroup (Matrix ι ι R)ˣ) : Prop :=
  ∀ (i j : ι) (hij : i ≠ j) (a : R), elementaryUnit i j hij a ∈ H → a = 0

variable {H : Subgroup (Matrix ι ι R)ˣ}

/-- **A column transvection in `H` is trivial.** -/
theorem colMatrix_eq_zero_of_mem (hnorm : PreusserNormalizedBy.NormalizedBy H (elementaryGroup ι R))
    (hno : NoTransvection H) (hcard : 3 ≤ Fintype.card ι) {g : (Matrix ι ι R)ˣ} (hg : g ∈ H)
    {j : ι} {w : ι → R} (hwj : w j = 0)
    (hval : (g : Matrix ι ι R) = 1 + ElementarySimplicity.colMatrix j w) : ∀ q, w q = 0 := by
  intro q
  by_cases hqj : q = j
  · rw [hqj, hwj]
  obtain ⟨p, hpq, hpj⟩ := exists_third_index hcard q j
  have hWW : ElementarySimplicity.colMatrix j w * ElementarySimplicity.colMatrix j w = 0 := by
    rw [ElementarySimplicity.colMatrix_mul_colMatrix, hwj]
    exact ElementarySimplicity.colMatrix_eq_zero j _ fun x => mul_zero (w x)
  have hWS : ElementarySimplicity.colMatrix j w * Matrix.single p q (1 : R) = 0 :=
    ElementarySimplicity.colMatrix_mul_single_of_ne j w p q 1 hpj
  have hSW : Matrix.single p q (1 : R) * ElementarySimplicity.colMatrix j w =
      Matrix.single p j (1 * w q) :=
    ElementarySimplicity.single_mul_colMatrix p q 1 j w
  have hSS : Matrix.single p q (1 : R) * Matrix.single p q (1 : R) = 0 :=
    single_mul_self_eq_zero p q hpq 1
  have hSWS : Matrix.single p q (1 : R) * ElementarySimplicity.colMatrix j w *
      Matrix.single p q (1 : R) = 0 := by
    rw [hSW]
    exact Matrix.single_mul_single_of_ne (c := 1 * w q) p j p hpj.symm (1 : R)
  have hinv : ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) = 1 - ElementarySimplicity.colMatrix j w := by
    have h1 : (1 - ElementarySimplicity.colMatrix j w) * (1 + ElementarySimplicity.colMatrix j w) =
        1 := by
      have e : (1 - ElementarySimplicity.colMatrix j w) * (1 + ElementarySimplicity.colMatrix j w) =
          1 - ElementarySimplicity.colMatrix j w * ElementarySimplicity.colMatrix j w := by
        noncomm_ring
      rw [e, hWW, sub_zero]
    calc ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)
        = (1 - ElementarySimplicity.colMatrix j w) * (1 + ElementarySimplicity.colMatrix j w) *
            ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) := by rw [h1, one_mul]
      _ = (1 - ElementarySimplicity.colMatrix j w) *
            ((g : Matrix ι ι R) * ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) := by
          rw [hval, mul_assoc]
      _ = 1 - ElementarySimplicity.colMatrix j w := by rw [Units.mul_inv, mul_one]
  have hk : ⁅g, elementaryUnit p q hpq 1⁆ ∈ H :=
    hnorm.commutator_mem_left hg (elementaryUnit_mem p q hpq 1)
  have hkval : ⁅g, elementaryUnit p q hpq 1⁆ = (elementaryUnit p j hpj (1 * w q))⁻¹ := by
    apply Units.ext
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul, hval, hinv]
    show (1 + ElementarySimplicity.colMatrix j w) * (1 + Matrix.single p q (1 : R)) *
        (1 - ElementarySimplicity.colMatrix j w) * (1 - Matrix.single p q (1 : R)) =
      1 - Matrix.single p j (1 * w q)
    rw [one_add_mul_one_add_mul_one_sub_mul_one_sub _ _ hWW hWS hSS hSWS, hSW]
  have hmem : elementaryUnit p j hpj (1 * w q) ∈ H := by
    have h := H.inv_mem hk
    rwa [hkval, inv_inv] at h
  have h0 := hno p j hpj (1 * w q) hmem
  rwa [one_mul] at h0

/-- **An element of `H` with a unit row is trivial.** -/
theorem eq_one_of_row_eq_one (hnorm : PreusserNormalizedBy.NormalizedBy H (elementaryGroup ι R))
    (hno : NoTransvection H) (hcard : 3 ≤ Fintype.card ι) {g : (Matrix ι ι R)ˣ} (hg : g ∈ H)
    {j : ι} (hrow : ∀ b, (g : Matrix ι ι R) j b = (1 : Matrix ι ι R) j b) : g = 1 := by
  have hrowinv : ∀ b, ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j b = (1 : Matrix ι ι R) j b := by
    intro b
    have h := mul_apply_of_row_eq_one (N := ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) hrow b
    rw [Units.mul_inv] at h
    exact h.symm
  -- the columns off `j`
  have hcol : ∀ l, l ≠ j → ∀ a, (g : Matrix ι ι R) a l = (1 : Matrix ι ι R) a l := by
    intro l hlj
    have hk : ⁅g, elementaryUnit l j hlj 1⁆ ∈ H :=
      hnorm.commutator_mem_left hg (elementaryUnit_mem l j hlj 1)
    have hV : (g : Matrix ι ι R) * Matrix.single l j (1 : R) *
        ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
          ElementarySimplicity.colMatrix j (fun a => (g : Matrix ι ι R) a l * 1) := by
      rw [ElementarySimplicity.mul_single_eq]
      ext a b
      rw [colMatrix_mul_apply, hrowinv b, ElementarySimplicity.colMatrix_apply, Matrix.one_apply]
      by_cases hb : b = j
      · subst hb
        simp
      · rw [if_neg (Ne.symm hb), if_neg hb, mul_zero]
    have hval : ((⁅g, elementaryUnit l j hlj 1⁆ : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
        1 + ElementarySimplicity.colMatrix j
          (fun a => (g : Matrix ι ι R) a l * 1 - (1 : Matrix ι ι R) a l) := by
      rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
      show (g : Matrix ι ι R) * (1 + Matrix.single l j (1 : R)) *
          ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) * (1 - Matrix.single l j (1 : R)) = _
      rw [RowAnnihilator.conj_val_eq _ _ _ (Units.mul_inv g), hV,
        one_add_colMatrix_mul_one_sub_single j l hlj]
    have hw := colMatrix_eq_zero_of_mem hnorm hno hcard hk
      (w := fun a => (g : Matrix ι ι R) a l * 1 - (1 : Matrix ι ι R) a l)
      (by simp only [hrow l, mul_one, sub_self]) hval
    intro a
    have ha : (g : Matrix ι ι R) a l * 1 - (1 : Matrix ι ι R) a l = 0 := hw a
    rwa [mul_one, sub_eq_zero] at ha
  -- column `j`
  have hval : (g : Matrix ι ι R) = 1 + ElementarySimplicity.colMatrix j
      (fun a => (g : Matrix ι ι R) a j - (1 : Matrix ι ι R) a j) := by
    ext a b
    rw [Matrix.add_apply, ElementarySimplicity.colMatrix_apply]
    by_cases hb : b = j
    · rw [if_pos hb, hb]
      abel
    · rw [if_neg hb, add_zero, hcol b hb a]
  have hw := colMatrix_eq_zero_of_mem hnorm hno hcard hg
    (w := fun a => (g : Matrix ι ι R) a j - (1 : Matrix ι ι R) a j)
    (by simp only [hrow j, sub_self]) hval
  apply Units.ext
  ext a b
  rw [Units.val_one]
  by_cases hb : b = j
  · rw [hb]
    exact sub_eq_zero.mp (hw a)
  · exact hcol b hb a

/-- A zero entry at `(j, k)` makes an element of `H` commute with every `e_{km}(x)`. -/
theorem commute_single_of_entry_eq_zero
    (hnorm : PreusserNormalizedBy.NormalizedBy H (elementaryGroup ι R)) (hno : NoTransvection H)
    (hcard : 3 ≤ Fintype.card ι) {g : (Matrix ι ι R)ˣ} (hg : g ∈ H) {j k : ι} (hjk : j ≠ k)
    (hzero : (g : Matrix ι ι R) j k = 0) (m : ι) (hkm : k ≠ m) (x : R) :
    (g : Matrix ι ι R) * Matrix.single k m x = Matrix.single k m x * (g : Matrix ι ι R) := by
  have hk : ⁅g, elementaryUnit k m hkm x⁆ ∈ H :=
    hnorm.commutator_mem_left hg (elementaryUnit_mem k m hkm x)
  have hval : ((⁅g, elementaryUnit k m hkm x⁆ : (Matrix ι ι R)ˣ) : Matrix ι ι R) =
      (1 + (g : Matrix ι ι R) * Matrix.single k m x * ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) *
        (1 - Matrix.single k m x) := by
    rw [commutatorElement_def, Units.val_mul, Units.val_mul, Units.val_mul]
    show (g : Matrix ι ι R) * (1 + Matrix.single k m x) * ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) *
        (1 - Matrix.single k m x) = _
    rw [RowAnnihilator.conj_val_eq _ _ _ (Units.mul_inv g)]
  have hrow : ∀ b, ((⁅g, elementaryUnit k m hkm x⁆ : (Matrix ι ι R)ˣ) : Matrix ι ι R) j b =
      (1 : Matrix ι ι R) j b := by
    intro b
    have hr : ∀ c, (1 + (g : Matrix ι ι R) * Matrix.single k m x *
        ((g⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R)) j c = (1 : Matrix ι ι R) j c := by
      intro c
      rw [Matrix.add_apply, RowAnnihilator.triple_single_apply, hzero, zero_mul, zero_mul, add_zero]
    rw [hval, mul_apply_of_row_eq_one hr b, Matrix.sub_apply,
      Matrix.single_apply_of_row_ne hjk.symm, sub_zero]
  have h1 := eq_one_of_row_eq_one hnorm hno hcard hk hrow
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  have h2 := congrArg (fun u : (Matrix ι ι R)ˣ => (u : Matrix ι ι R)) h1
  simp only [Units.val_mul] at h2
  change (g : Matrix ι ι R) * (1 + Matrix.single k m x) =
    (1 + Matrix.single k m x) * (g : Matrix ι ι R) at h2
  rw [mul_add, add_mul, mul_one, one_mul] at h2
  exact add_left_cancel h2

/-- **Lemma 4.1 at a unit column**: a zero off-diagonal entry makes an element of `H` central. -/
theorem mem_congruenceSubgroup_bot_of_entry_eq_zero
    (hnorm : PreusserNormalizedBy.NormalizedBy H (elementaryGroup ι R)) (hno : NoTransvection H)
    (hcard : 3 ≤ Fintype.card ι) {g : (Matrix ι ι R)ˣ} (hg : g ∈ H) {j k : ι} (hjk : j ≠ k)
    (hzero : (g : Matrix ι ι R) j k = 0) : g ∈ congruenceSubgroup ι (⊥ : TwoSidedIdeal R) := by
  have hall : ∀ (q m : ι) (hqm : q ≠ m) (x : R),
      (g : Matrix ι ι R) * Matrix.single q m x = Matrix.single q m x * (g : Matrix ι ι R) := by
    intro q m hqm x
    by_cases hqk : q = k
    · subst hqk
      exact commute_single_of_entry_eq_zero hnorm hno hcard hg hjk hzero m hqm x
    · obtain ⟨p, hpk, hpq⟩ := exists_third_index hcard k q
      have hc := commute_single_of_entry_eq_zero hnorm hno hcard hg hjk hzero p (Ne.symm hpk) 1
      have hpq0 : (g : Matrix ι ι R) p q = 0 := by
        have h := congrFun (congrFun hc k) q
        rw [ElementarySimplicity.mul_single_apply, ElementarySimplicity.single_mul_apply,
          if_neg (Ne.symm hpq), if_pos rfl, one_mul] at h
        exact h.symm
      exact commute_single_of_entry_eq_zero hnorm hno hcard hg hpq hpq0 m hqm x
  have hcard1 : 1 < Fintype.card ι := by omega
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hdiag := eq_diagonal_of_commute_single hcard1 i₀ (g : Matrix ι ι R)
    fun i j hij => hall i j hij 1
  refine mem_congruenceSubgroup.mpr ⟨(g : Matrix ι ι R) i₀ i₀, mem_relativeCenter_bot.mpr ?_,
    fun a b => ?_⟩
  · intro x
    refine commute_of_commute_single hcard1 _ (fun i j a hij => ?_) x
    rw [← hdiag]
    exact hall i j hij a
  · rw [← hdiag, sub_self, Matrix.zero_apply]
    exact TwoSidedIdeal.zero_mem _

end StepanovMatui
end Full
end GroupApproximation

#audit_axioms GroupApproximation.Full.StepanovMatui.colMatrix_eq_zero_of_mem
#audit_axioms GroupApproximation.Full.StepanovMatui.eq_one_of_row_eq_one
#audit_axioms GroupApproximation.Full.StepanovMatui.mem_congruenceSubgroup_bot_of_entry_eq_zero
