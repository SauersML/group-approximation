import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.PermutationAdjointGap

/-!
# The adjoint estimates *require* operator-norm multiplicative control

Proof-ledger row `LI.16`, probe `p:limits-models`.  The limitations section of
`non_mf_groups_exist.tex` closes its comparison with Alekseev--Thom's Open
Problem 6.2 with a sentence about the *method* (grep the tex for
`"require operator-norm multiplicative control"`):

> Their question concerns Hamming and tracial models, whereas the adjoint
> spectral estimates here require operator-norm multiplicative control, which
> permutation and Hilbert--Schmidt models do not supply.

The row has stood at `MISMATCH` on its statement column for the reason its own
note gives: *no declaration says of the method that it requires operator-norm
control; what is proved is the counterexample that makes the sentence true.*
This file removes that reason.

## "Requires" as a proposition

A hypothesis is *required* when the conclusion follows from it and follows from
nothing weaker in the direction at issue.  So the sentence is three statements,
and `adjointEstimates_require_operatorNormMultiplicativeControl` is their
conjunction:

1. **Operator-norm control supplies the estimate.**
   `AdjointMatrix.l2_opNorm_conjDouble_sub_le_two`: `‖Ad U - Ad V‖ ≤ 2‖U - V‖`
   for unitaries, with no dimension loss.
2. **Hilbert--Schmidt models do not.**
   `HilbertSchmidtAdjointGap.no_vanishing_modulus_controls_adjoint`: *no*
   vanishing modulus at all controls the adjoint defect through the normalized
   Hilbert--Schmidt distance.
3. **Permutation models do not.**  `no_vanishing_modulus_controls_adjoint_hamming`,
   proved here, is the same for the normalized *Hamming* distance --- the
   metric permutation models actually come with, and the one Alekseev--Thom's
   problem is posed in.

## What is new here, against what was already proved

`Sofic/PermutationAdjointGap.lean` already refutes every vanishing modulus for
permutation models measured in the normalized *Hilbert--Schmidt* distance, and
its docstring calls that "equivalently, Hamming".  Two things were missing and
are supplied here.

*The Hamming statement itself.*  `hammingDistance_one_swap` computes the
normalized Hamming distance from `1` to a transposition, and
`exists_hammingClose_adjointFar` and `no_vanishing_modulus_controls_adjoint_hamming`
are the Hamming forms.  The bridge in the other direction is the repository's
`Hyperlinear.permMatrix_hsDistSq`, recorded here as
`hsNormSq_permMatrix_sub_eq`, which is what makes the parenthetical
"equivalently" a theorem rather than a remark.

*The sharp constant.*  `PermutationAdjointGap.one_le_l2_opNorm_conjDouble_sub_perm`
records `1`, from the witness `e_{i₀i₀} ↦ e_{i₁i₁}`, which gives ratio `√2`.
The witness `e_{i₀i₀} - e_{i₁i₁}` does better: a transposition *negates* it, so
the ratio is `2` --- exactly the constant of the positive estimate in item 1.
`two_le_l2_opNorm_conjDouble_sub_perm` is that bound.  So the gap between the
two sides is not an artifact of a lossy constant: `2` is simultaneously the
sharp upper bound in operator norm and a lower bound here, at every dimension.

Two conventions for permutation matrices meet in this file --- Mathlib's
`Equiv.Perm.permMatrix` (used by `Hyperlinear` and by
`Analysis/AmenableQuasidiagonal`) and `PermutationAdjointGap.permMatrix`
(written out there to avoid relying on a library convention).  They agree, by
`permMatrix_eq`, and everything below is stated in Mathlib's.

## What is not claimed

Nothing here bears on Alekseev--Thom's Open Problem 6.2, which is open and is
recorded as such in `notes/NON_MF_META_CLAIMS.md` (row `LI.05` is its
tombstone).  What is proved is the manuscript's stated *reason* for the two
problems being different.

The multiplicative form of the sentence is `exists_hammingDefect_and_adjointDefect`:
a permutation model whose multiplicativity defect is below any prescribed
Hamming tolerance can still have adjoint multiplicativity defect `2` in
operator norm.  It is not an independent phenomenon --- `conjDouble` is exactly
multiplicative (`conjDouble_mul`), so an adjoint multiplicativity defect is an
adjoint distance --- but it is the form the printed sentence asserts, and the
printed word is *multiplicative*.
-/

namespace GroupApproximation
namespace AdjointOperatorNormRequirement

open Matrix KazhdanCornerMatrices HilbertSchmidtAdjointGap PermutationAdjointGap
open scoped Matrix.Norms.L2Operator

noncomputable section

section General

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-! ## The two permutation-matrix conventions agree -/

omit [Fintype Y] in
/-- Entries of Mathlib's permutation matrix, at an arbitrary finite coordinate
type: `Hyperlinear.permMatrixC_entry` with the `FiniteModel` bundling
dropped. -/
theorem permMatrix_entry (σ : Equiv.Perm Y) (x y : Y) :
    (σ.permMatrix ℂ) x y = if σ x = y then (1 : ℂ) else 0 := by
  simp [Equiv.Perm.permMatrix]

omit [Fintype Y] in
/-- `PermutationAdjointGap` writes its own permutation matrix rather than rely
on a library convention; it is Mathlib's. -/
theorem permMatrix_eq (σ : Equiv.Perm Y) :
    PermutationAdjointGap.permMatrix σ = σ.permMatrix ℂ := by
  ext i j
  rw [PermutationAdjointGap.permMatrix_apply, permMatrix_entry]
  by_cases hji : j = σ i
  · rw [if_pos hji, if_pos hji.symm]
  · rw [if_neg hji, if_neg fun hij ↦ hji hij.symm]

/-! ## The sharp constant -/

/-- A vector that a conjugation *negates*, and that carries Frobenius mass `2`,
forces adjoint distance `2` --- the constant of the positive operator-norm
estimate itself.  Stated for an arbitrary `U` so that both the transposition
below and any future witness can use it. -/
private theorem two_le_l2_opNorm_of_conj_neg {A U : Matrix Y Y ℂ}
    (hmass : ∑ i : Y, ∑ j : Y, Complex.normSq (A i j) = 2)
    (hconj : U * A * Uᴴ = -A) :
    (2 : ℝ) ≤ ‖conjDouble (1 : Matrix Y Y ℂ) - conjDouble U‖ := by
  classical
  have hone : conjDouble (1 : Matrix Y Y ℂ) *ᵥ rowVec A = rowVec A := by
    rw [conjDouble_mulVec_rowVec]
    simp
  have hU : conjDouble U *ᵥ rowVec A = rowVec (-A) := by
    rw [conjDouble_mulVec_rowVec, hconj]
  have hdiff : (conjDouble (1 : Matrix Y Y ℂ) - conjDouble U) *ᵥ rowVec A
      = rowVec ((2 : ℂ) • A) := by
    rw [Matrix.sub_mulVec, hone, hU]
    funext p
    simp only [rowVec, Pi.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
      smul_eq_mul]
    ring
  have hpt : ∀ p : Y × Y, Complex.normSq (rowVec ((2 : ℂ) • A) p)
      = 4 * Complex.normSq (rowVec A p) := by
    intro p
    simp only [rowVec, Matrix.smul_apply, smul_eq_mul]
    rw [Complex.normSq_mul, normSq_two]
  have hmassRight : ∑ p : Y × Y, Complex.normSq (rowVec A p) = 2 := by
    rw [sum_normSq_rowVec, hmass]
  have hmassLeft : ∑ p : Y × Y, Complex.normSq
      (((conjDouble (1 : Matrix Y Y ℂ) - conjDouble U) *ᵥ rowVec A) p) = 8 := by
    have hstep : ∑ p : Y × Y, Complex.normSq
        (((conjDouble (1 : Matrix Y Y ℂ) - conjDouble U) *ᵥ rowVec A) p)
        = ∑ p : Y × Y, 4 * Complex.normSq (rowVec A p) := by
      rw [hdiff]
      exact Finset.sum_congr rfl fun p _ ↦ hpt p
    rw [hstep, ← Finset.mul_sum, hmassRight]
    norm_num
  have hbound := sum_normSq_mulVec_le_general
    (conjDouble (1 : Matrix Y Y ℂ) - conjDouble U) (rowVec A)
  rw [hmassLeft, hmassRight] at hbound
  nlinarith [norm_nonneg (conjDouble (1 : Matrix Y Y ℂ) - conjDouble U)]

/-- **A transposition negates the traceless diagonal `e_{i₀i₀} - e_{i₁i₁}`.**
It exchanges the two diagonal units, and they enter with opposite signs. -/
theorem swap_conj_unitMatrix_sub (i₀ i₁ : Y) :
    PermutationAdjointGap.permMatrix (Equiv.swap i₀ i₁)
        * (unitMatrix i₀ i₀ - unitMatrix i₁ i₁)
        * (PermutationAdjointGap.permMatrix (Equiv.swap i₀ i₁))ᴴ
      = -(unitMatrix i₀ i₀ - unitMatrix i₁ i₁) := by
  have h2 : PermutationAdjointGap.permMatrix (Equiv.swap i₀ i₁)
      * unitMatrix i₁ i₁
      * (PermutationAdjointGap.permMatrix (Equiv.swap i₀ i₁))ᴴ
      = unitMatrix i₀ i₀ := by
    rw [Equiv.swap_comm]
    exact swap_conj_unitMatrix i₁ i₀
  rw [Matrix.mul_sub, Matrix.sub_mul, swap_conj_unitMatrix, h2, neg_sub]

/-- **The adjoints of `1` and of a transposition stay `2` apart**, in every
dimension.  This is `PermutationAdjointGap.one_le_l2_opNorm_conjDouble_sub_perm`
at the sharp constant: `2` is also the upper bound of the positive
operator-norm estimate, so the two sides of the comparison meet exactly. -/
theorem two_le_l2_opNorm_conjDouble_sub_perm {i₀ i₁ : Y} (h : i₀ ≠ i₁) :
    (2 : ℝ) ≤ ‖conjDouble (1 : Matrix Y Y ℂ)
      - conjDouble ((Equiv.swap i₀ i₁).permMatrix ℂ)‖ := by
  rw [← permMatrix_eq]
  exact two_le_l2_opNorm_of_conj_neg (sum_normSq_unitMatrix_sub h)
    (swap_conj_unitMatrix_sub i₀ i₁)

end General

/-! ## The Hamming metric of a permutation model -/

/-- **"Equivalently, Hamming."**  The squared normalized Hilbert--Schmidt
distance between two permutation matrices is twice the normalized Hamming
distance between the permutations.  This is `Hyperlinear.permMatrix_hsDistSq`
in the `hsNormSq`-of-a-difference form, which is the form the modulus
statements are written in; `hsDistSq Y A B` is definitionally
`hsNormSq Y (A - B)`. -/
theorem hsNormSq_permMatrix_sub_eq (Y : FiniteModel) (σ τ : Equiv.Perm Y) :
    hsNormSq Y (σ.permMatrix ℂ - τ.permMatrix ℂ) = 2 * hammingDistance Y σ τ :=
  permMatrix_hsDistSq Y σ τ

/-- The normalized Hamming distance from the identity to a transposition is
`2/d`. -/
theorem hammingDistance_one_swap (Y : FiniteModel) {i₀ i₁ : Y} (h : i₀ ≠ i₁) :
    hammingDistance Y 1 (Equiv.swap i₀ i₁) = 2 / (Fintype.card Y : ℝ) := by
  classical
  have hsupp : ((Equiv.swap i₀ i₁)⁻¹ * 1 : Equiv.Perm Y).support.card = 2 := by
    rw [Equiv.swap_inv, mul_one]
    exact Equiv.Perm.card_support_swap h
  rw [hammingDistance_eq_support, hsupp]
  norm_num

/-- The model construction shared by the two witness statements: a
transposition in a model large enough for its normalized Hamming distance to
sit below a prescribed tolerance. -/
private theorem exists_model_swap (ε : ℝ) (hε : 0 < ε) :
    ∃ (Y : FiniteModel) (i₀ i₁ : Y), i₀ ≠ i₁ ∧
      hammingDistance Y 1 (Equiv.swap i₀ i₁) ≤ ε := by
  obtain ⟨d, hd⟩ := exists_nat_gt (2 / ε)
  have hzero : (0 : ℕ) < d + 2 := by omega
  have hone : (1 : ℕ) < d + 2 := by omega
  have hne : (⟨0, hzero⟩ : Fin (d + 2)) ≠ (⟨1, hone⟩ : Fin (d + 2)) := by simp
  refine ⟨naturalFiniteModel (d + 2), (⟨0, hzero⟩ : Fin (d + 2)),
    (⟨1, hone⟩ : Fin (d + 2)), hne, ?_⟩
  rw [hammingDistance_one_swap _ hne]
  have hcard :
      (Fintype.card (naturalFiniteModel (d + 2)) : ℝ) = (d : ℝ) + 2 := by
    simp
  have hpos : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have h2 : (2 : ℝ) < (d : ℝ) * ε := (div_lt_iff₀ hε).mp hd
  rw [hcard, div_le_iff₀ hpos]
  nlinarith

/-- **Hamming control does not transfer to the adjoints.**  For every
tolerance there are a finite model and two permutations whose normalized
Hamming distance is below that tolerance, while their conjugation operators on
the Hilbert--Schmidt space differ by at least `2` in operator norm. -/
theorem exists_hammingClose_adjointFar :
    ∀ ε : ℝ, 0 < ε → ∃ (Y : FiniteModel) (σ τ : Equiv.Perm Y),
      hammingDistance Y σ τ ≤ ε ∧
      2 ≤ ‖conjDouble (σ.permMatrix ℂ) - conjDouble (τ.permMatrix ℂ)‖ := by
  intro ε hε
  obtain ⟨Y, i₀, i₁, hne, hdist⟩ := exists_model_swap ε hε
  refine ⟨Y, 1, Equiv.swap i₀ i₁, hdist, ?_⟩
  rw [Matrix.permMatrix_one]
  exact two_le_l2_opNorm_conjDouble_sub_perm hne

/-- **No vanishing modulus controls the adjoint defect from Hamming
closeness.**  There is no function `m` with `m δ → 0` as `δ → 0⁺` bounding the
adjoint defect of two permutation matrices whose normalized Hamming distance is
at most `δ`: by `exists_hammingClose_adjointFar` the defect stays at `2` at
every tolerance, while a vanishing modulus is eventually below `2`.

This is `PermutationAdjointGap.no_vanishing_modulus_controls_adjoint_perm` in
the metric permutation models actually supply. -/
theorem no_vanishing_modulus_controls_adjoint_hamming :
    ¬ ∃ m : ℝ → ℝ,
      Filter.Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      ∀ (Y : FiniteModel) (σ τ : Equiv.Perm Y) (δ : ℝ), 0 < δ →
        hammingDistance Y σ τ ≤ δ →
          ‖conjDouble (σ.permMatrix ℂ) - conjDouble (τ.permMatrix ℂ)‖
            ≤ m δ := by
  rintro ⟨m, hm, hcontrol⟩
  have hIio : ∀ᶠ s in nhds (0 : ℝ), s < 2 := by
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)] with s hs
    exact hs
  have h2 : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0), m δ < 2 := hm.eventually hIio
  obtain ⟨δ, hδ2, hδmem⟩ := (h2.and eventually_mem_nhdsWithin).exists
  have hδpos : 0 < δ := Set.mem_Ioi.mp hδmem
  obtain ⟨Y, σ, τ, hdist, hfar⟩ := exists_hammingClose_adjointFar δ hδpos
  have := hcontrol Y σ τ δ hδpos hdist
  linarith

/-- **The multiplicative form.**  For every tolerance there is a permutation
model whose multiplicativity defect is below that tolerance in normalized
Hamming distance, while the multiplicativity defect of the induced adjoint
model is at least `2` in operator norm.  The witnesses are `σ = τ = 1` and `ρ`
a transposition, whose Hamming defect against `σ τ = 1` is `2/d`. -/
theorem exists_hammingDefect_and_adjointDefect :
    ∀ ε : ℝ, 0 < ε → ∃ (Y : FiniteModel) (σ τ ρ : Equiv.Perm Y),
      hammingDistance Y ρ (σ * τ) ≤ ε ∧
      2 ≤ ‖conjDouble (ρ.permMatrix ℂ) -
        conjDouble (σ.permMatrix ℂ) * conjDouble (τ.permMatrix ℂ)‖ := by
  intro ε hε
  obtain ⟨Y, i₀, i₁, hne, hdist⟩ := exists_model_swap ε hε
  refine ⟨Y, 1, 1, Equiv.swap i₀ i₁, ?_, ?_⟩
  · rw [mul_one, hammingDistance_comm]
    exact hdist
  · rw [Matrix.permMatrix_one, ← conjDouble_mul, mul_one, ← norm_neg, neg_sub]
    exact two_le_l2_opNorm_conjDouble_sub_perm hne

/-! ## The printed sentence -/

/-- **The adjoint spectral estimates require operator-norm multiplicative
control, which permutation and Hilbert--Schmidt models do not supply.**

The three conjuncts are the three assertions the sentence makes, in the order
it makes them.

1. Operator-norm control *supplies* the estimate, with the linear modulus `2`
   and no dimension loss.
2. Hilbert--Schmidt models do not: no vanishing modulus at all --- however
   weak --- controls the adjoint defect through the normalized
   Hilbert--Schmidt distance.
3. Permutation models do not: the same, in the normalized Hamming distance,
   with permutation matrices as the witnesses.

Paired with conjunct 1, conjuncts 2 and 3 are what "requires" asserts: the
hypothesis is used, and it cannot be weakened to either of the two hypotheses
Alekseev--Thom's Open Problem 6.2 is posed with. -/
theorem adjointEstimates_require_operatorNormMultiplicativeControl :
    (∀ (Y : FiniteModel) (U V : Matrix Y Y ℂ),
        U ∈ Matrix.unitaryGroup Y ℂ → V ∈ Matrix.unitaryGroup Y ℂ →
        ‖conjDouble U - conjDouble V‖ ≤ 2 * ‖U - V‖) ∧
      (¬ ∃ m : ℝ → ℝ,
        Filter.Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        ∀ (Y : FiniteModel) (U V : Matrix Y Y ℂ),
          U ∈ Matrix.unitaryGroup Y ℂ → V ∈ Matrix.unitaryGroup Y ℂ →
          ∀ δ : ℝ, 0 < δ → Real.sqrt (hsNormSq Y (U - V)) ≤ δ →
            ‖conjDouble U - conjDouble V‖ ≤ m δ) ∧
      (¬ ∃ m : ℝ → ℝ,
        Filter.Tendsto m (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        ∀ (Y : FiniteModel) (σ τ : Equiv.Perm Y) (δ : ℝ), 0 < δ →
          hammingDistance Y σ τ ≤ δ →
            ‖conjDouble (σ.permMatrix ℂ) - conjDouble (τ.permMatrix ℂ)‖
              ≤ m δ) :=
  ⟨fun _ _ _ hU hV ↦ l2_opNorm_conjDouble_sub_le_two hU hV,
    HilbertSchmidtAdjointGap.no_vanishing_modulus_controls_adjoint,
    no_vanishing_modulus_controls_adjoint_hamming⟩

end

end AdjointOperatorNormRequirement
end GroupApproximation
