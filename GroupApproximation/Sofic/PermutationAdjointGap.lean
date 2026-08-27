import GroupApproximation.Sofic.HilbertSchmidtAdjointGap

/-!
# Permutation models do not supply operator-norm control either

Proof-ledger row `LI.16`.  The limitations section says the adjoint spectral
estimates require *operator-norm* multiplicative control, and that

> permutation and Hilbert--Schmidt models do not supply [it].

`Sofic/HilbertSchmidtAdjointGap.lean` settles the Hilbert--Schmidt half, and
settles it about the method rather than about a pair of witnesses:
`no_vanishing_modulus_controls_adjoint` rules out *every* vanishing modulus.
Its witness is a sign diagonal, which is a unitary but not a permutation
matrix, so it says nothing about the permutation half --- and permutation
models are the ones soficity actually supplies.

This file closes that half with the same shape of argument.  The witness is
the cheapest permutation available: `1` against a transposition.

* `permMatrix (Equiv.swap i₀ i₁)` differs from `1` in exactly four entries, of
  modulus `1` each, so its Frobenius mass is `4` in every dimension and its
  normalized Hilbert--Schmidt distance is `2/√d`, which goes to zero;
* but conjugation by a permutation permutes matrix units --- `perm_conj_apply`
  is the one-line calculation `(P A P⋆)_{ab} = A_{σa,σb}` --- so a
  transposition carries the diagonal unit `e_{i₀i₀}` to `e_{i₁i₁}`, the
  difference `e_{i₀i₀} - e_{i₁i₁}` has Frobenius mass `2` against the unit
  mass of `e_{i₀i₀}`, and the operator norm is bounded below independently of
  the dimension.

The lower bound recorded here is `1` rather than the sharp `√2`, because any
dimension-free positive constant refutes every vanishing modulus, which is
what `no_vanishing_modulus_controls_adjoint_perm` states and all the printed
sentence needs.

## Manuscript status

With `HilbertSchmidtAdjointGap`, this completes the printed sentence of
`p:limits-models` about what the two model classes fail to supply.
-/

namespace GroupApproximation
namespace PermutationAdjointGap

open Matrix KazhdanCornerMatrices HilbertSchmidtAdjointGap
open scoped Matrix.Norms.L2Operator

noncomputable section

section General

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## Permutation matrices and conjugation -/

/-- The permutation matrix of `σ`, written out so that no convention for a
library permutation matrix is relied on. -/
def permMatrix (σ : Equiv.Perm Y) : Matrix Y Y ℂ :=
  Matrix.of fun i j ↦ if j = σ i then 1 else 0

omit [Fintype Y] in
@[simp] theorem permMatrix_apply (σ : Equiv.Perm Y) (i j : Y) :
    permMatrix σ i j = if j = σ i then 1 else 0 := rfl

/-- Left multiplication by a permutation matrix permutes rows. -/
theorem permMatrix_mul_apply (σ : Equiv.Perm Y) (A : Matrix Y Y ℂ) (a t : Y) :
    (permMatrix σ * A) a t = A (σ a) t := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
  · rw [permMatrix_apply, if_pos rfl, one_mul]
  · intro s _ hs
    rw [permMatrix_apply, if_neg hs, zero_mul]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- Right multiplication by the adjoint of a permutation matrix permutes
columns. -/
theorem mul_permMatrix_conjTranspose_apply (σ : Equiv.Perm Y)
    (A : Matrix Y Y ℂ) (a b : Y) :
    (A * (permMatrix σ)ᴴ) a b = A a (σ b) := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ b)]
  · rw [Matrix.conjTranspose_apply, permMatrix_apply, if_pos rfl]
    simp
  · intro t _ ht
    rw [Matrix.conjTranspose_apply, permMatrix_apply, if_neg ht]
    simp
  · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- **Conjugation by a permutation matrix permutes matrix entries.** -/
theorem perm_conj_apply (σ : Equiv.Perm Y) (A : Matrix Y Y ℂ) (a b : Y) :
    (permMatrix σ * A * (permMatrix σ)ᴴ) a b = A (σ a) (σ b) := by
  rw [mul_permMatrix_conjTranspose_apply, permMatrix_mul_apply]

/-- Conjugation by a transposition moves the diagonal matrix unit at `i₀` to
the one at `i₁`. -/
theorem swap_conj_unitMatrix (i₀ i₁ : Y) :
    permMatrix (Equiv.swap i₀ i₁) * unitMatrix i₀ i₀
        * (permMatrix (Equiv.swap i₀ i₁))ᴴ
      = unitMatrix i₁ i₁ := by
  classical
  have hsymm : (Equiv.swap i₀ i₁).symm i₀ = i₁ := by
    rw [Equiv.symm_swap]
    exact Equiv.swap_apply_left i₀ i₁
  have hiff : ∀ z : Y, (Equiv.swap i₀ i₁ z = i₀) ↔ (z = i₁) := by
    intro z
    rw [Equiv.apply_eq_iff_eq_symm_apply, hsymm]
  ext a b
  rw [perm_conj_apply, unitMatrix_apply, unitMatrix_apply]
  by_cases ha : a = i₁ <;> by_cases hb : b = i₁ <;>
    simp [hiff, ha, hb]

/-! ## The two Frobenius masses -/

omit [Fintype Y] in
/-- Entries of the difference of `1` and a permutation matrix. -/
theorem one_sub_permMatrix_apply (σ : Equiv.Perm Y) (i j : Y) :
    ((1 : Matrix Y Y ℂ) - permMatrix σ) i j
      = (if j = i then (1 : ℂ) else 0) - (if j = σ i then (1 : ℂ) else 0) := by
  classical
  rw [Matrix.sub_apply, Matrix.one_apply, permMatrix_apply]
  by_cases hji : j = i
  · simp [hji]
  · simp [hji, Ne.symm hji]

/-- `1` and a transposition matrix differ in exactly four entries of modulus
one. -/
theorem sum_normSq_one_sub_permSwap {i₀ i₁ : Y} (h : i₀ ≠ i₁) :
    ∑ i : Y, ∑ j : Y, Complex.normSq
        (((1 : Matrix Y Y ℂ) - permMatrix (Equiv.swap i₀ i₁)) i j) = 4 := by
  classical
  have hrow : ∀ i : Y, ∑ j : Y, Complex.normSq
      (((1 : Matrix Y Y ℂ) - permMatrix (Equiv.swap i₀ i₁)) i j)
      = if i = i₀ ∨ i = i₁ then (2 : ℝ) else 0 := by
    intro i
    by_cases hi : i = i₀ ∨ i = i₁
    · rw [if_pos hi]
      have hne : Equiv.swap i₀ i₁ i ≠ i := by
        rcases hi with rfl | rfl
        · rw [Equiv.swap_apply_left]; exact h.symm
        · rw [Equiv.swap_apply_right]; exact h
      have hsupp : ∀ j : Y,
          j ∈ (Finset.univ : Finset Y) →
          j ∉ ({i, Equiv.swap i₀ i₁ i} : Finset Y) →
          Complex.normSq
            (((1 : Matrix Y Y ℂ)
              - permMatrix (Equiv.swap i₀ i₁)) i j) = 0 := by
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        rw [one_sub_permMatrix_apply, if_neg hj.1, if_neg hj.2, sub_zero,
          map_zero]
      rw [← Finset.sum_subset (Finset.subset_univ
        ({i, Equiv.swap i₀ i₁ i} : Finset Y)) hsupp]
      rw [Finset.sum_pair (Ne.symm hne)]
      rw [one_sub_permMatrix_apply, one_sub_permMatrix_apply]
      rw [if_pos rfl, if_neg hne, if_pos rfl, if_neg (Ne.symm hne)]
      simp
      norm_num
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun j _ ↦ ?_
      have hfix : Equiv.swap i₀ i₁ i = i := by
        rcases not_or.mp hi with ⟨h1, h2⟩
        exact Equiv.swap_apply_of_ne_of_ne h1 h2
      rw [one_sub_permMatrix_apply, hfix, sub_self, map_zero]
  rw [Finset.sum_congr rfl fun i _ ↦ hrow i]
  have hsupp : ∀ i : Y, i ∈ (Finset.univ : Finset Y) →
      i ∉ ({i₀, i₁} : Finset Y) →
      (if i = i₀ ∨ i = i₁ then (2 : ℝ) else 0) = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact if_neg (by tauto)
  rw [← Finset.sum_subset (Finset.subset_univ ({i₀, i₁} : Finset Y)) hsupp]
  rw [Finset.sum_pair h]
  norm_num

/-- The difference of two distinct diagonal matrix units carries Frobenius
mass `2`. -/
theorem sum_normSq_unitMatrix_sub {i₀ i₁ : Y} (h : i₀ ≠ i₁) :
    ∑ i : Y, ∑ j : Y,
        Complex.normSq ((unitMatrix i₀ i₀ - unitMatrix i₁ i₁) i j) = 2 := by
  classical
  have hentry : ∀ i j : Y, (unitMatrix i₀ i₀ - unitMatrix i₁ i₁) i j
      = (if i = i₀ ∧ j = i₀ then (1 : ℂ) else 0)
        - (if i = i₁ ∧ j = i₁ then (1 : ℂ) else 0) := by
    intro i j
    rw [Matrix.sub_apply, unitMatrix_apply, unitMatrix_apply]
  have hrow : ∀ i : Y, ∑ j : Y,
      Complex.normSq ((unitMatrix i₀ i₀ - unitMatrix i₁ i₁) i j)
      = if i = i₀ ∨ i = i₁ then (1 : ℝ) else 0 := by
    intro i
    by_cases hi₀ : i = i₀
    · subst hi₀
      rw [if_pos (Or.inl rfl), Finset.sum_eq_single i]
      · rw [hentry i i, if_pos ⟨rfl, rfl⟩, if_neg (by tauto), sub_zero]
        simp
      · intro j _ hj
        rw [hentry i j, if_neg (by tauto), if_neg (by tauto), sub_zero,
          map_zero]
      · intro hmem; exact absurd (Finset.mem_univ _) hmem
    · by_cases hi₁ : i = i₁
      · subst hi₁
        rw [if_pos (Or.inr rfl), Finset.sum_eq_single i]
        · rw [hentry i i, if_neg (by tauto), if_pos ⟨rfl, rfl⟩, zero_sub]
          simp
        · intro j _ hj
          rw [hentry i j, if_neg (by tauto), if_neg (by tauto), sub_zero,
            map_zero]
        · intro hmem; exact absurd (Finset.mem_univ _) hmem
      · rw [if_neg (by tauto)]
        refine Finset.sum_eq_zero fun j _ ↦ ?_
        rw [hentry i j, if_neg (by tauto), if_neg (by tauto), sub_zero,
          map_zero]
  rw [Finset.sum_congr rfl fun i _ ↦ hrow i]
  have hsupp : ∀ i : Y, i ∈ (Finset.univ : Finset Y) →
      i ∉ ({i₀, i₁} : Finset Y) →
      (if i = i₀ ∨ i = i₁ then (1 : ℝ) else 0) = 0 := by
    intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact if_neg (by tauto)
  rw [← Finset.sum_subset (Finset.subset_univ ({i₀, i₁} : Finset Y)) hsupp]
  rw [Finset.sum_pair h]
  norm_num

/-! ## The operator-norm lower bound -/

/-- **The adjoint operators of `1` and of a transposition stay apart**, with
no dependence on the dimension. -/
theorem one_le_l2_opNorm_conjDouble_sub_perm {i₀ i₁ : Y} (h : i₀ ≠ i₁) :
    (1 : ℝ) ≤ ‖conjDouble (1 : Matrix Y Y ℂ)
      - conjDouble (permMatrix (Equiv.swap i₀ i₁))‖ := by
  classical
  have hone : conjDouble (1 : Matrix Y Y ℂ) *ᵥ rowVec (unitMatrix i₀ i₀) =
      rowVec (unitMatrix i₀ i₀) := by
    rw [conjDouble_mulVec_rowVec]
    simp
  have hperm : conjDouble (permMatrix (Equiv.swap i₀ i₁)) *ᵥ
      rowVec (unitMatrix i₀ i₀) = rowVec (unitMatrix i₁ i₁) := by
    rw [conjDouble_mulVec_rowVec, swap_conj_unitMatrix i₀ i₁]
  have hdiff : (conjDouble (1 : Matrix Y Y ℂ)
        - conjDouble (permMatrix (Equiv.swap i₀ i₁))) *ᵥ
      rowVec (unitMatrix i₀ i₀)
      = rowVec (unitMatrix i₀ i₀ - unitMatrix i₁ i₁) := by
    rw [Matrix.sub_mulVec, hone, hperm]
    funext p
    rfl
  have hmassRight : ∑ p : Y × Y,
      Complex.normSq (rowVec (unitMatrix i₀ i₀) p) = 1 := by
    rw [sum_normSq_rowVec, sum_normSq_unitMatrix]
  have hmassLeft : ∑ p : Y × Y, Complex.normSq
      (((conjDouble (1 : Matrix Y Y ℂ)
        - conjDouble (permMatrix (Equiv.swap i₀ i₁))) *ᵥ
        rowVec (unitMatrix i₀ i₀)) p) = 2 := by
    rw [hdiff, sum_normSq_rowVec, sum_normSq_unitMatrix_sub h]
  have hbound := sum_normSq_mulVec_le_general
    (conjDouble (1 : Matrix Y Y ℂ)
      - conjDouble (permMatrix (Equiv.swap i₀ i₁)))
    (rowVec (unitMatrix i₀ i₀))
  rw [hmassLeft, hmassRight, mul_one] at hbound
  nlinarith [norm_nonneg (conjDouble (1 : Matrix Y Y ℂ)
    - conjDouble (permMatrix (Equiv.swap i₀ i₁)))]

end General

/-! ## The manuscript's statement -/

/-- The normalized Hilbert--Schmidt distance between `1` and a transposition
matrix is `4 / d`. -/
theorem hsNormSq_one_sub_permSwap (Y : FiniteModel) {i₀ i₁ : Y}
    (h : i₀ ≠ i₁) :
    hsNormSq Y ((1 : Matrix Y Y ℂ) - permMatrix (Equiv.swap i₀ i₁))
      = 4 / (Fintype.card Y : ℝ) := by
  simp only [hsNormSq]
  rw [sum_normSq_one_sub_permSwap h]

/-- **Permutation models do not transfer Hilbert--Schmidt control to the
adjoints.**  For every tolerance there are two permutations of some finite
model whose matrices are within that normalized Hilbert--Schmidt distance
while their adjoint operators differ by at least `1` in operator norm. -/
theorem exists_permClose_adjointFar :
    ∀ ε : ℝ, 0 < ε → ∃ (Y : FiniteModel) (σ τ : Equiv.Perm Y),
      Real.sqrt (hsNormSq Y (permMatrix σ - permMatrix τ)) ≤ ε ∧
      1 ≤ ‖conjDouble (permMatrix σ) - conjDouble (permMatrix τ)‖ := by
  intro ε hε
  obtain ⟨d, hd⟩ := exists_nat_gt (4 / ε ^ 2)
  have hzero : (0 : ℕ) < d + 2 := by omega
  have hone : (1 : ℕ) < d + 2 := by omega
  have hne : (⟨0, hzero⟩ : Fin (d + 2)) ≠ (⟨1, hone⟩ : Fin (d + 2)) := by
    simp
  have hperm1 : permMatrix (1 : Equiv.Perm (naturalFiniteModel (d + 2)))
      = (1 : Matrix (naturalFiniteModel (d + 2))
          (naturalFiniteModel (d + 2)) ℂ) := by
    ext a b
    rw [permMatrix_apply, Matrix.one_apply]
    simp [eq_comm]
  refine ⟨naturalFiniteModel (d + 2), 1,
    Equiv.swap (⟨0, hzero⟩ : Fin (d + 2)) (⟨1, hone⟩ : Fin (d + 2)),
    ?_, ?_⟩
  · rw [hperm1]
    have hcard :
        (Fintype.card (naturalFiniteModel (d + 2)) : ℝ) = (d : ℝ) + 2 := by
      simp
    have hpos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
    have hεsq : (0 : ℝ) < ε ^ 2 := by positivity
    have hlt : 4 / ε ^ 2 < (d : ℝ) + 2 := by
      have hdd : (4 : ℝ) / ε ^ 2 < (d : ℝ) := hd
      linarith
    rw [div_lt_iff₀ hεsq] at hlt
    have hle : hsNormSq (naturalFiniteModel (d + 2))
        ((1 : Matrix (naturalFiniteModel (d + 2))
          (naturalFiniteModel (d + 2)) ℂ)
          - permMatrix (Equiv.swap (⟨0, hzero⟩ : Fin (d + 2))
              (⟨1, hone⟩ : Fin (d + 2)))) ≤ ε ^ 2 := by
      rw [hsNormSq_one_sub_permSwap _ hne, hcard, div_le_iff₀ hpos]
      nlinarith
    calc
      Real.sqrt (hsNormSq (naturalFiniteModel (d + 2))
          ((1 : Matrix (naturalFiniteModel (d + 2))
            (naturalFiniteModel (d + 2)) ℂ)
            - permMatrix (Equiv.swap (⟨0, hzero⟩ : Fin (d + 2))
                (⟨1, hone⟩ : Fin (d + 2)))))
          ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hle
      _ = ε := Real.sqrt_sq hε.le
  · rw [hperm1]
    exact one_le_l2_opNorm_conjDouble_sub_perm
      (i₁ := (⟨1, hone⟩ : Fin (d + 2))) hne

/-- **No vanishing modulus controls the adjoint defect from Hilbert--Schmidt
closeness of permutation models.**  This is the permutation half of the
printed sentence: the adjoint spectral estimates cannot be routed through the
normalized Hilbert--Schmidt --- equivalently, Hamming --- distance of the
permutations, however weak the modulus. -/
theorem no_vanishing_modulus_controls_adjoint_perm :
    ¬ ∃ m : ℝ → ℝ,
      Filter.Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ (Y : FiniteModel) (σ τ : Equiv.Perm Y) (δ : ℝ), 0 < δ →
        Real.sqrt (hsNormSq Y (permMatrix σ - permMatrix τ)) ≤ δ →
          ‖conjDouble (permMatrix σ) - conjDouble (permMatrix τ)‖ ≤ m δ := by
  rintro ⟨m, hm, hcontrol⟩
  have hIio : ∀ᶠ s in nhds (0 : ℝ), s < 1 := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)] with s hs
    exact hs
  have h1 : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), m δ < 1 := hm.eventually hIio
  obtain ⟨δ, hδ1, hδmem⟩ := (h1.and eventually_mem_nhdsWithin).exists
  have hδpos : 0 < δ := Set.mem_Ioi.mp hδmem
  obtain ⟨Y, σ, τ, hdist, hfar⟩ := exists_permClose_adjointFar δ hδpos
  have := hcontrol Y σ τ δ hδpos hdist
  linarith

end

end PermutationAdjointGap
end GroupApproximation
