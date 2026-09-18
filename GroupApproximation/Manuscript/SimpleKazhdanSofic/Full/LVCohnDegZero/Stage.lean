import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
import GroupApproximation.Algebra.LocallyMatricial
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnDegZero.Defs
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnDegZero.Fock

/-!
# The finite stages of the degree-zero part of `C₂(𝔽₂)`

The `n`-th stage of the degree-zero part `C₀` of the Cohn algebra `C₂(𝔽₂)` is spanned by
* the matrix units `e_{μν} = x_μ p y_ν` with `|μ| = |ν| = j < n`, and
* the elements `x_μ y_ν` with `|μ| = |ν| = n`.

These form a system of matrix units of shape `(2^0, 2^1, …, 2^n)`, whose diagonal adds up to
`1 = ∑_{j<n} ∑_{|μ|=j} e_{μμ} + ∑_{|μ|=n} x_μ y_μ`.  So the `n`-th stage is a unital
subring isomorphic to `∏_{j ≤ n} M_{2^j}(𝔽₂)` (Ara-Brustenga-Cortiñas 2009, Sec. 5 and the
proof of Thm 3.6; `simple_kazhdan_sofic_group.tex` l.733-735, `sec:questions`,
leaf T1b.iii).
-/

namespace GroupApproximation.Full.LVCohnDegZero

open GroupApproximation.Full.LVCohnRelK1

noncomputable section

/-! ### Words of length `j`, indexed by `Fin (2 ^ j)` -/

theorem card_word (j : ℕ) : Fintype.card (Fin j → Bool) = 2 ^ j := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- An enumeration of the binary words of length `j`. -/
def wordEquiv (j : ℕ) : Fin (2 ^ j) ≃ (Fin j → Bool) :=
  (Fintype.equivFinOfCardEq (card_word j)).symm

/-- The `a`-th binary word of length `j`. -/
def vw (j : ℕ) (a : Fin (2 ^ j)) : List Bool := List.ofFn (wordEquiv j a)

theorem vw_length (j : ℕ) (a : Fin (2 ^ j)) : (vw j a).length = j := by
  rw [vw]
  exact List.length_ofFn

theorem vw_injective (j : ℕ) : Function.Injective (vw j) := fun _ _ h =>
  (wordEquiv j).injective (List.ofFn_injective h)

theorem exists_vw (μ : List Bool) : ∃ a : Fin (2 ^ μ.length), vw μ.length a = μ :=
  ⟨(wordEquiv μ.length).symm μ.get, by rw [vw, Equiv.apply_symm_apply, List.ofFn_get]⟩

/-! ### Sums over all words of length `j` -/

/-- `∑_{|μ| = j} G μ`. -/
def wsum (j : ℕ) (G : List Bool → CohnTwoF2) : CohnTwoF2 :=
  ∑ f : Fin j → Bool, G (List.ofFn f)

theorem sum_vw (j : ℕ) (G : List Bool → CohnTwoF2) :
    ∑ a : Fin (2 ^ j), G (vw j a) = wsum j G :=
  Equiv.sum_comp (wordEquiv j) (fun f => G (List.ofFn f))

theorem wsum_zero (G : List Bool → CohnTwoF2) : wsum 0 G = G [] := by
  rw [wsum, Fintype.sum_unique, List.ofFn_zero]

/-- A binary word of length `j + 1` is a first letter followed by a word of length `j`. -/
def consBoolEquiv (j : ℕ) : Bool × (Fin j → Bool) ≃ (Fin (j + 1) → Bool) :=
  Fin.consEquiv fun _ : Fin (j + 1) => Bool

theorem consBoolEquiv_apply (j : ℕ) (b : Bool) (f : Fin j → Bool) :
    consBoolEquiv j (b, f) = Fin.cons b f :=
  rfl

/-- If `G (b :: μ) = x_b G(μ) y_b`, then `∑_{|μ|=j+1} G μ = ∑_b x_b (∑_{|μ|=j} G μ) y_b`. -/
theorem wsum_succ (G : List Bool → CohnTwoF2)
    (hG : ∀ (b : Bool) (μ : List Bool), G (b :: μ) = cx b * G μ * cy b) (j : ℕ) :
    wsum (j + 1) G = cx true * wsum j G * cy true + cx false * wsum j G * cy false := by
  have h1 : wsum (j + 1) G =
      ∑ p : Bool × (Fin j → Bool), G (List.ofFn (consBoolEquiv j p)) :=
    (Equiv.sum_comp (consBoolEquiv j) fun f => G (List.ofFn f)).symm
  have h2 : ∀ b : Bool, ∑ f : Fin j → Bool, G (List.ofFn (consBoolEquiv j (b, f))) =
      cx b * wsum j G * cy b := by
    intro b
    rw [wsum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [consBoolEquiv_apply, List.ofFn_cons, hG]
  rw [h1, Fintype.sum_prod_type, Fintype.sum_bool, h2, h2]

/-! ### The diagonal and the decomposition of `1` -/

/-- The diagonal matrix unit `e_{μμ} = x_μ p y_μ`. -/
def diagU (μ : List Bool) : CohnTwoF2 := unitE μ μ

/-- The diagonal idempotent `x_μ y_μ`. -/
def diagV (μ : List Bool) : CohnTwoF2 := xw μ * yw μ

theorem diagU_cons (b : Bool) (μ : List Bool) : diagU (b :: μ) = cx b * diagU μ * cy b := by
  rw [diagU, diagU, cx_mul_unitE, unitE_mul_cy]

theorem diagV_cons (b : Bool) (μ : List Bool) : diagV (b :: μ) = cx b * diagV μ * cy b := by
  rw [diagV, diagV, xw_cons, yw_cons]
  simp only [mul_assoc]

/-- `1 = ∑_{j<n} ∑_{|μ|=j} e_{μμ} + ∑_{|μ|=n} x_μ y_μ`. -/
theorem total_eq_one : ∀ n : ℕ, ∑ j : Fin n, wsum j.val diagU + wsum n diagV = 1
  | 0 => by rw [Fin.sum_univ_zero, zero_add, wsum_zero, diagV, xw_nil, yw_nil, one_mul]
  | n + 1 => by
    have ih := total_eq_one n
    have key : ∀ b : Bool, ∑ j : Fin n, cx b * wsum j.val diagU * cy b +
        cx b * wsum n diagV * cy b = cx b * cy b := by
      intro b
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← add_mul, ← mul_add, ih, mul_one]
    have hsplit : ∑ j : Fin (n + 1), wsum j.val diagU = cohnP + ∑ j : Fin n,
        (cx true * wsum j.val diagU * cy true + cx false * wsum j.val diagU * cy false) := by
      rw [Fin.sum_univ_succ]
      congr 1
      · exact (wsum_zero diagU).trans unitE_nil_nil
      · exact Finset.sum_congr rfl fun j _ => wsum_succ diagU diagU_cons j.val
    rw [hsplit, wsum_succ diagV diagV_cons n, Finset.sum_add_distrib, add_assoc cohnP,
      add_add_add_comm, key true, key false, cohnP_def, sub_sub,
      add_comm (cx true * cy true), sub_add_cancel]

/-! ### The matrix units of the `n`-th stage -/

/-- The target `∏_{j ≤ n} M_{2^j}(𝔽₂)` of the `n`-th stage. -/
abbrev StageAlg (n : ℕ) : Type :=
  (j : Fin (n + 1)) → Matrix (Fin (2 ^ j.val)) (Fin (2 ^ j.val)) (ZMod 2)

/-- The matrix units of the `n`-th stage: `e_{μν}` in the blocks `j < n` and `x_μ y_ν` in the
last block `j = n`. -/
def stageUnit (n : ℕ) (j : Fin (n + 1)) (a b : Fin (2 ^ j.val)) : CohnTwoF2 :=
  if j.val < n then unitE (vw j.val a) (vw j.val b) else xw (vw j.val a) * yw (vw j.val b)

theorem stageUnit_of_lt {n : ℕ} {j : Fin (n + 1)} (h : j.val < n) (a b : Fin (2 ^ j.val)) :
    stageUnit n j a b = unitE (vw j.val a) (vw j.val b) := by
  rw [stageUnit, if_pos h]

theorem stageUnit_of_not_lt {n : ℕ} {j : Fin (n + 1)} (h : ¬j.val < n)
    (a b : Fin (2 ^ j.val)) :
    stageUnit n j a b = xw (vw j.val a) * yw (vw j.val b) := by
  rw [stageUnit, if_neg h]

theorem xy_mul_xy (A B C : List Bool) : xw A * yw B * (xw B * yw C) = xw A * yw C := by
  rw [mul_assoc, ← mul_assoc (yw B), yw_mul_xw_self, one_mul]

theorem xy_mul_xy_of_ne (A B B' C : List Bool) (hl : B.length = B'.length) (h : B ≠ B') :
    xw A * yw B * (xw B' * yw C) = 0 := by
  rw [mul_assoc, ← mul_assoc (yw B), yw_mul_xw_of_ne B B' hl h, zero_mul, mul_zero]

theorem unitE_mul_xy_of_lt (A B C D : List Bool) (h : B.length < C.length) :
    unitE A B * (xw C * yw D) = 0 := by
  rw [unitE_def]
  simp only [mul_assoc]
  rw [← mul_assoc (yw B) (xw C) (yw D), ← mul_assoc cohnP (yw B * xw C) (yw D),
    cohnP_mul_yw_mul_xw_of_lt B C h, zero_mul, mul_zero]

theorem xy_mul_unitE_of_lt (A B C D : List Bool) (h : C.length < B.length) :
    xw A * yw B * unitE C D = 0 := by
  rw [unitE_def]
  simp only [mul_assoc]
  rw [← mul_assoc (xw C) cohnP (yw D), ← mul_assoc (yw B) (xw C * cohnP) (yw D),
    ← mul_assoc (yw B) (xw C) cohnP, yw_mul_xw_mul_cohnP_of_lt B C h, zero_mul, mul_zero]

theorem unitE_self_ne_zero (A : List Bool) : unitE A A ≠ 0 := by
  intro h0
  apply cohnP_ne_zero
  have h : yw A * unitE A A * xw A = cohnP := by
    rw [unitE_def]
    simp only [mul_assoc]
    rw [← mul_assoc (yw A) (xw A), yw_mul_xw_self, one_mul, mul_one]
  rw [← h, h0, mul_zero, zero_mul]

theorem xy_self_ne_zero (A : List Bool) : xw A * yw A ≠ 0 := by
  intro h0
  apply cohn_one_ne_zero
  have h : yw A * (xw A * yw A) * xw A = 1 := by
    simp only [mul_assoc]
    rw [yw_mul_xw_self, mul_one, yw_mul_xw_self]
  rw [← h, h0, mul_zero, zero_mul]

/-- The elements `stageUnit n` form a matrix unit family of shape `(2^j)_{j ≤ n}`. -/
theorem stageUnit_isFamily (n : ℕ) : ChainCore.IsMatrixUnitFamily (stageUnit n) where
  mul_same j a b c := by
    by_cases hj : j.val < n
    · simp only [stageUnit_of_lt hj]
      rw [unitE_mul_unitE, if_pos rfl]
    · simp only [stageUnit_of_not_lt hj]
      exact xy_mul_xy _ _ _
  mul_of_ne j a b b' c hbb' := by
    have hne : vw j.val b ≠ vw j.val b' := fun h => hbb' (vw_injective _ h)
    by_cases hj : j.val < n
    · simp only [stageUnit_of_lt hj]
      rw [unitE_mul_unitE, if_neg hne]
    · simp only [stageUnit_of_not_lt hj]
      exact xy_mul_xy_of_ne _ _ _ _ ((vw_length _ b).trans (vw_length _ b').symm) hne
  mul_of_block_ne i j hij a b c d := by
    have hlen : ∀ (x : Fin (2 ^ i.val)) (y : Fin (2 ^ j.val)), vw i.val x ≠ vw j.val y := by
      intro x y h
      have hl := congrArg List.length h
      rw [vw_length, vw_length] at hl
      exact hij (Fin.ext hl)
    by_cases hi : i.val < n
    · by_cases hj : j.val < n
      · rw [stageUnit_of_lt hi, stageUnit_of_lt hj, unitE_mul_unitE, if_neg (hlen b c)]
      · rw [stageUnit_of_lt hi, stageUnit_of_not_lt hj]
        apply unitE_mul_xy_of_lt
        rw [vw_length, vw_length]
        omega
    · by_cases hj : j.val < n
      · rw [stageUnit_of_not_lt hi, stageUnit_of_lt hj]
        apply xy_mul_unitE_of_lt
        rw [vw_length, vw_length]
        omega
      · exfalso
        apply hij
        apply Fin.ext
        have hi' := i.isLt
        have hj' := j.isLt
        omega

theorem stageUnit_diag_ne_zero (n : ℕ) (j : Fin (n + 1)) (a : Fin (2 ^ j.val)) :
    stageUnit n j a a ≠ 0 := by
  by_cases hj : j.val < n
  · rw [stageUnit_of_lt hj]
    exact unitE_self_ne_zero _
  · rw [stageUnit_of_not_lt hj]
    exact xy_self_ne_zero _

end

end GroupApproximation.Full.LVCohnDegZero
