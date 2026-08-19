/-
The two quantities defined here, and the identity relating them, are the
statement-level design of Section 4 of

  Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, Henry Yuen,
  "Quantum soundness of the classical low individual degree test",
  arXiv:2009.12982,

the technical core of MIP* = RE.  There the whole soundness argument is carried
in two numbers attached to a pair of outcome families -- how much mass they put
on *disagreeing* outcomes (consistency) and how far apart they are in the
state-dependent distance -- and the argument's first move is that for
projective families these are the same number up to a factor of two.

A Lean formalization of that development exists as `LionSR/MIPStarRE`, the
source of the Palomar registry entry PALOMAR-2026-08-18-000001.  That
repository carries no licence, so nothing here is copied from it; the proofs
below are written for this repository, and the setting is deliberately
different.  There the state is a vector state on a bipartite space; here it is
the normalized trace of a finite model, which is the state every microstate in
`Sofic.Sofic` already carries, so the calculus lands directly on the objects
this development is about rather than on a translation of them.
-/

import GroupApproximation.Sofic.HyperlinearScalar
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Consistency is closeness

Two families `A B : α → Matrix Y Y ℂ` of *effects* on a finite model -- think
of the outcome operators of two finite-dimensional measurements with the same
outcome set `α` -- can be compared in two ways.

* The **state-dependent distance** `sdDistSq Y A B = ∑ₐ ‖Aₐ - Bₐ‖²`, in the
  normalized Hilbert-Schmidt norm of `Sofic.HyperlinearScalar`.  This is the
  quantity a rounding argument wants: it is what "the two measurements are
  interchangeable" means quantitatively, and it composes along a chain.

* The **consistency defect** `consDefect Y A B`, the mass the pair places on
  *disagreeing* outcomes: the total overlap `Re τ(A_tot B_totᴴ)` minus the
  matching mass `∑ₐ Re τ(Aₐ Bₐᴴ)`.  This is the quantity a *test* measures --
  it is an average of "did the two answers agree", and it is what a hypothesis
  about a near-representation actually hands you.

The point of the file is that the two are the same thing:

* `sdDistSq_eq_two_mul_consDefect` -- for **projective** families summing to
  `1`, exactly `sdDistSq = 2 · consDefect`;
* `sdDistSq_le_two_mul_consDefect` -- for families of **effects** `0 ≤ E ≤ 1`
  summing to `1`, the inequality `sdDistSq ≤ 2 · consDefect`, in the useful
  direction: a test that sees agreement has certified closeness.

Neither statement needs `0 < card Y`.  Both sides are computed from the same
`normTrace Y 1`, so the degenerate model cancels rather than having to be
excluded.

`sdDistSq_triangle` is the composition rule, in the squared form
`d(A,C) ≤ 2 d(A,B) + 2 d(B,C)`: no square roots, and no norm instance on
matrices, matching how `hsNormSq` is used everywhere else here.

The inequality for effects rests on `hsNormSq_le_normTrace_re`, that
`τ(E²) ≤ τ(E)` when `0 ≤ E ≤ 1`, proved from the identity

  `E - E² = E(1-E)E + (1-E)E(1-E)`,

which exhibits it as a sum of two congruences of positive semidefinite matrices
and so needs no square root, no spectral theorem and no functional calculus.
-/

namespace GroupApproximation

open Matrix
open scoped ComplexOrder

namespace ConsistencyDistance

variable {α : Type*} [Fintype α]

/-! ## The two quantities -/

/-- `∑ₐ Aₐ`, the total of an outcome family.  A measurement is a family whose
total is `1`. -/
noncomputable def total (Y : FiniteModel) (A : α → Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  ∑ a, A a

/-- The state-dependent squared distance `∑ₐ ‖Aₐ - Bₐ‖²` in the normalized
Hilbert-Schmidt norm. -/
noncomputable def sdDistSq (Y : FiniteModel) (A B : α → Matrix Y Y ℂ) : ℝ :=
  ∑ a, hsNormSq Y (A a - B a)

/-- The matching mass `∑ₐ Re τ(Aₐ Bₐᴴ)`: the mass the two families place on the
*same* outcome. -/
noncomputable def matchMass (Y : FiniteModel) (A B : α → Matrix Y Y ℂ) : ℝ :=
  ∑ a, (normTrace Y (A a * (B a)ᴴ)).re

/-- The consistency defect: total overlap minus matching mass, i.e. the mass
the pair places on disagreeing outcomes. -/
noncomputable def consDefect (Y : FiniteModel) (A B : α → Matrix Y Y ℂ) : ℝ :=
  (normTrace Y (total Y A * (total Y B)ᴴ)).re - matchMass Y A B

/-! ## The normalized Hilbert-Schmidt norm as a real trace -/

/-- `‖A‖² = Re τ(A Aᴴ)`.  The squared norm is already real, so this only names
the real part. -/
theorem hsNormSq_eq_normTrace_re (Y : FiniteModel) (A : Matrix Y Y ℂ) :
    hsNormSq Y A = (normTrace Y (A * Aᴴ)).re := by
  rw [← ofReal_hsNormSq]
  simp

omit [Fintype α] in
/-- The normalized trace of a finite sum. -/
theorem normTrace_sum (Y : FiniteModel) (s : Finset α) (f : α → Matrix Y Y ℂ) :
    normTrace Y (∑ a ∈ s, f a) = ∑ a ∈ s, normTrace Y (f a) := by
  simp only [normTrace, Matrix.trace_sum, Finset.sum_div]

/-- **Polarization.**  `‖A - B‖² = ‖A‖² + ‖B‖² - 2 Re τ(A Bᴴ)`. -/
theorem hsNormSq_sub (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    hsNormSq Y (A - B)
      = hsNormSq Y A + hsNormSq Y B - 2 * (normTrace Y (A * Bᴴ)).re := by
  have hexp : (A - B) * (A - B)ᴴ
      = A * Aᴴ + B * Bᴴ - (A * Bᴴ + B * Aᴴ) := by
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  have hconj : normTrace Y (B * Aᴴ) = (starRingEnd ℂ) (normTrace Y (A * Bᴴ)) := by
    have h : (A * Bᴴ)ᴴ = B * Aᴴ := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [normTrace, ← h, Matrix.trace_conjTranspose, map_div₀,
      starRingEnd_apply, star_natCast]
  have htr : Matrix.trace ((A - B) * (A - B)ᴴ)
      = Matrix.trace (A * Aᴴ) + Matrix.trace (B * Bᴴ)
        - (Matrix.trace (A * Bᴴ) + Matrix.trace (B * Aᴴ)) := by
    rw [hexp, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_add]
  have hnt : normTrace Y ((A - B) * (A - B)ᴴ)
      = normTrace Y (A * Aᴴ) + normTrace Y (B * Bᴴ)
        - (normTrace Y (A * Bᴴ) + normTrace Y (B * Aᴴ)) := by
    simp only [normTrace, htr]
    ring
  have hC : ((hsNormSq Y (A - B) : ℝ) : ℂ)
      = ((hsNormSq Y A : ℝ) : ℂ) + ((hsNormSq Y B : ℝ) : ℂ)
        - ((2 * (normTrace Y (A * Bᴴ)).re : ℝ) : ℂ) := by
    rw [ofReal_hsNormSq, ofReal_hsNormSq, ofReal_hsNormSq, hnt, hconj,
      Complex.add_conj]
  exact_mod_cast hC

/-! ## The distance, expanded -/

theorem sdDistSq_eq (Y : FiniteModel) (A B : α → Matrix Y Y ℂ) :
    sdDistSq Y A B
      = (∑ a, hsNormSq Y (A a)) + (∑ a, hsNormSq Y (B a))
        - 2 * matchMass Y A B := by
  simp only [sdDistSq, matchMass, hsNormSq_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

theorem sdDistSq_nonneg (Y : FiniteModel) (A B : α → Matrix Y Y ℂ) :
    0 ≤ sdDistSq Y A B :=
  Finset.sum_nonneg fun _ _ ↦ hsNormSq_nonneg Y _

theorem sdDistSq_self (Y : FiniteModel) (A : α → Matrix Y Y ℂ) :
    sdDistSq Y A A = 0 := by
  simp [sdDistSq, hsNormSq]

theorem sdDistSq_comm (Y : FiniteModel) (A B : α → Matrix Y Y ℂ) :
    sdDistSq Y A B = sdDistSq Y B A := by
  -- `hsNormSq_neg` is proved in `Sofic.UltraproductKazhdanTransport`, which
  -- this module deliberately does not import; the one line it costs here is
  -- cheaper than the dependency, and the audit's duplicate scan reads
  -- declarations, not `have`s.
  have hneg : ∀ X : Matrix Y Y ℂ, hsNormSq Y (-X) = hsNormSq Y X := by
    intro X
    simp [hsNormSq]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← hneg (A a - B a), neg_sub]

/-- **Composition.**  The squared distance obeys the quadratic triangle
inequality, which is all a chain of rounding steps ever needs. -/
theorem sdDistSq_triangle (Y : FiniteModel) (A B C : α → Matrix Y Y ℂ) :
    sdDistSq Y A C ≤ 2 * sdDistSq Y A B + 2 * sdDistSq Y B C := by
  simp only [sdDistSq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ ↦ ?_
  rw [← sub_add_sub_cancel (A a) (B a) (C a)]
  exact hsNormSq_add_le Y _ _

/-! ## Effects: `τ(E²) ≤ τ(E)` -/

/-- The real part of a normalized trace of a positive semidefinite matrix is
nonnegative -- including on the empty model, where both sides are zero because
`normTrace` divides by a cardinality of zero. -/
theorem normTrace_re_nonneg_of_posSemidef (Y : FiniteModel) {Z : Matrix Y Y ℂ}
    (hZ : Z.PosSemidef) : 0 ≤ (normTrace Y Z).re := by
  have htr : (0 : ℂ) ≤ Matrix.trace Z := hZ.trace_nonneg
  have htr' : 0 ≤ (Matrix.trace Z).re := by
    simpa using (Complex.le_def.mp htr).1
  rcases Nat.eq_zero_or_pos (Fintype.card Y) with hcard | hcard
  · simp [normTrace, hcard]
  · rw [normTrace, div_natCast_re _ hcard.ne']
    positivity

/-- **The effect inequality.**  If `0 ≤ E` and `E ≤ 1` then `τ(E²) ≤ τ(E)`.

The proof is the identity `E - E² = E(1-E)E + (1-E)E(1-E)`, which writes the
difference as a sum of two congruences of positive semidefinite matrices.  No
square root, no spectral theorem and no functional calculus is involved. -/
theorem hsNormSq_le_normTrace_re (Y : FiniteModel) {E : Matrix Y Y ℂ}
    (hE : E.PosSemidef) (hE1 : (1 - E).PosSemidef) :
    hsNormSq Y E ≤ (normTrace Y E).re := by
  have hEh : Eᴴ = E := hE.isHermitian
  have h1h : (1 - E)ᴴ = 1 - E := hE1.isHermitian
  have hdecomp : E - E * E
      = Eᴴ * (1 - E) * E + (1 - E)ᴴ * E * (1 - E) := by
    rw [hEh, h1h]
    noncomm_ring
  have hpsd : (E - E * E).PosSemidef := by
    rw [hdecomp]
    exact (hE1.conjTranspose_mul_mul_same E).add (hE.conjTranspose_mul_mul_same (1 - E))
  have hnn : 0 ≤ (normTrace Y (E - E * E)).re :=
    normTrace_re_nonneg_of_posSemidef Y hpsd
  rw [normTrace_sub, Complex.sub_re] at hnn
  rw [hsNormSq_eq_normTrace_re, hEh]
  linarith

/-! ## Projections -/

/-- For a projection, the squared norm is the trace. -/
theorem hsNormSq_of_isProj (Y : FiniteModel) {P : Matrix Y Y ℂ}
    (hH : Pᴴ = P) (hI : P * P = P) :
    hsNormSq Y P = (normTrace Y P).re := by
  rw [hsNormSq_eq_normTrace_re, hH, hI]

/-! ## Consistency is closeness -/

/-- The mass a family of projections summing to `1` puts on the model. -/
private theorem sum_hsNormSq_of_isProj (Y : FiniteModel) (A : α → Matrix Y Y ℂ)
    (hH : ∀ a, (A a)ᴴ = A a) (hI : ∀ a, A a * A a = A a) :
    (∑ a, hsNormSq Y (A a)) = (normTrace Y (total Y A)).re := by
  rw [total, normTrace_sum, Complex.re_sum]
  exact Finset.sum_congr rfl fun a _ ↦ hsNormSq_of_isProj Y (hH a) (hI a)

private theorem sum_hsNormSq_le_of_effect (Y : FiniteModel) (A : α → Matrix Y Y ℂ)
    (hE : ∀ a, (A a).PosSemidef) (hE1 : ∀ a, (1 - A a).PosSemidef) :
    (∑ a, hsNormSq Y (A a)) ≤ (normTrace Y (total Y A)).re := by
  rw [total, normTrace_sum, Complex.re_sum]
  exact Finset.sum_le_sum fun a _ ↦ hsNormSq_le_normTrace_re Y (hE a) (hE1 a)

/-- **Consistency is closeness, exactly, for projective measurements.**

Two families of projections with total `1` are at squared distance exactly
twice their consistency defect.  This is the identity the whole rounding
programme runs on: a test statistic about *agreement of outcomes* and a
statement about *operators being close* are the same number. -/
theorem sdDistSq_eq_two_mul_consDefect (Y : FiniteModel) (A B : α → Matrix Y Y ℂ)
    (hAH : ∀ a, (A a)ᴴ = A a) (hAI : ∀ a, A a * A a = A a)
    (hBH : ∀ a, (B a)ᴴ = B a) (hBI : ∀ a, B a * B a = B a)
    (hAt : total Y A = 1) (hBt : total Y B = 1) :
    sdDistSq Y A B = 2 * consDefect Y A B := by
  rw [sdDistSq_eq, consDefect, sum_hsNormSq_of_isProj Y A hAH hAI,
    sum_hsNormSq_of_isProj Y B hBH hBI, hAt, hBt]
  simp only [Matrix.conjTranspose_one, one_mul]
  ring

/-- **Consistency certifies closeness, for measurements by effects.**

If both families consist of effects (`0 ≤ Eₐ ≤ 1`) and both total to `1`, the
squared distance is at most twice the consistency defect.  This is the
direction a soundness argument uses: a test that observes agreement has
certified that the two measurements are interchangeable. -/
theorem sdDistSq_le_two_mul_consDefect (Y : FiniteModel) (A B : α → Matrix Y Y ℂ)
    (hA : ∀ a, (A a).PosSemidef) (hA1 : ∀ a, (1 - A a).PosSemidef)
    (hB : ∀ a, (B a).PosSemidef) (hB1 : ∀ a, (1 - B a).PosSemidef)
    (hAt : total Y A = 1) (hBt : total Y B = 1) :
    sdDistSq Y A B ≤ 2 * consDefect Y A B := by
  have hA' := sum_hsNormSq_le_of_effect Y A hA hA1
  have hB' := sum_hsNormSq_le_of_effect Y B hB hB1
  rw [hAt] at hA'
  rw [hBt] at hB'
  rw [sdDistSq_eq, consDefect, hAt, hBt]
  simp only [Matrix.conjTranspose_one, one_mul]
  linarith

/-- The consistency defect of a pair of projective measurements is nonnegative:
it is half a squared distance. -/
theorem consDefect_nonneg_of_isProj (Y : FiniteModel) (A B : α → Matrix Y Y ℂ)
    (hAH : ∀ a, (A a)ᴴ = A a) (hAI : ∀ a, A a * A a = A a)
    (hBH : ∀ a, (B a)ᴴ = B a) (hBI : ∀ a, B a * B a = B a)
    (hAt : total Y A = 1) (hBt : total Y B = 1) :
    0 ≤ consDefect Y A B := by
  have h := sdDistSq_eq_two_mul_consDefect Y A B hAH hAI hBH hBI hAt hBt
  have := sdDistSq_nonneg Y A B
  linarith


/-! ## The classical case: consistency is Hamming distance

The definitions above are about operators, but they specialize to the objects
soficity is stated in.  A function `f : Y → α` -- a colouring of the model, or
the value of a permutation read at each point -- has a projective measurement
attached to it, the readout `Pᶠ_a = diagonal 1_{f = a}`, and the consistency
defect of two readouts is exactly the normalized Hamming distance between the
two functions.

So `sdDistSq_eq_two_mul_consDefect` says, in this case, that the
Hilbert-Schmidt distance between two classical readouts is twice their Hamming
distance -- and the general theorem is the statement that a *quantum*
measurement pair obeys the same law.  That is the sense in which the calculus
belongs here: the metric a near-action is measured in and the metric a rounding
argument produces are the same metric.
-/

section Readout

variable [DecidableEq α]

/-- The projective measurement that reads off the value of `f`. -/
noncomputable def readout (Y : FiniteModel) (f : Y → α) (a : α) : Matrix Y Y ℂ :=
  Matrix.diagonal fun y ↦ if f y = a then 1 else 0

omit [Fintype α] in
theorem readout_conjTranspose (Y : FiniteModel) (f : Y → α) (a : α) :
    (readout Y f a)ᴴ = readout Y f a := by
  rw [readout, Matrix.diagonal_conjTranspose]
  congr 1
  funext y
  by_cases h : f y = a <;> simp [h]

omit [Fintype α] in
theorem readout_mul_self (Y : FiniteModel) (f : Y → α) (a : α) :
    readout Y f a * readout Y f a = readout Y f a := by
  rw [readout, Matrix.diagonal_mul_diagonal]
  congr 1
  funext y
  by_cases h : f y = a <;> simp [h]

theorem readout_total (Y : FiniteModel) (f : Y → α) :
    total Y (readout Y f) = 1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [total, readout, Matrix.sum_apply, Matrix.diagonal_apply_eq,
      Matrix.one_apply_eq]
  · simp [total, readout, Matrix.sum_apply, Matrix.diagonal_apply_ne _ h,
      Matrix.one_apply_ne h]

omit [Fintype α] in
/-- The overlap of two readouts on one outcome counts the points where both
functions take that value. -/
private theorem trace_readout_mul (Y : FiniteModel) (f g : Y → α) (a : α) :
    Matrix.trace (readout Y f a * (readout Y g a)ᴴ)
      = ((Finset.univ.filter fun y ↦ f y = a ∧ g y = a).card : ℂ) := by
  rw [readout_conjTranspose, readout, readout, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases h1 : f y = a <;> by_cases h2 : g y = a <;> simp [h1, h2]

/-- Summing the outcomewise overlaps counts the points where the two functions
agree. -/
private theorem sum_agree_card (Y : FiniteModel) (f g : Y → α) :
    (∑ a : α, (Finset.univ.filter fun y ↦ f y = a ∧ g y = a).card)
      = (Finset.univ.filter fun y ↦ f y = g y).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases h : f y = g y
  · rw [Finset.sum_eq_single (f y)]
    · simp [h]
    · intro b _ hb
      simp only [ite_eq_right_iff]
      rintro ⟨hb', -⟩
      exact absurd hb'.symm hb
    · simp
  · refine (Finset.sum_eq_zero fun a _ ↦ ?_).trans (by simp [h])
    rcases eq_or_ne (f y) a with rfl | ha
    · simp only [ite_eq_right_iff]
      rintro ⟨-, hg⟩
      exact absurd hg.symm h
    · simp [ha]

/-- **The classical instance.**  The consistency defect of two readouts is the
normalized Hamming distance between the two functions. -/
theorem consDefect_readout (Y : FiniteModel) (f g : Y → α)
    (hY : 0 < Fintype.card Y) :
    consDefect Y (readout Y f) (readout Y g)
      = ((Finset.univ.filter fun y ↦ f y ≠ g y).card : ℝ) / Fintype.card Y := by
  have hne : (Fintype.card Y : ℕ) ≠ 0 := hY.ne'
  have hone : (normTrace Y (total Y (readout Y f) * (total Y (readout Y g))ᴴ)).re
      = 1 := by
    rw [readout_total, readout_total]
    simp only [Matrix.conjTranspose_one, one_mul, normTrace, Matrix.trace_one]
    rw [div_natCast_re _ hne]
    simp [hne]
  have hmatch : matchMass Y (readout Y f) (readout Y g)
      = ((Finset.univ.filter fun y ↦ f y = g y).card : ℝ) / Fintype.card Y := by
    rw [matchMass]
    have hterm : ∀ a : α, (normTrace Y (readout Y f a * (readout Y g a)ᴴ)).re
        = ((Finset.univ.filter fun y ↦ f y = a ∧ g y = a).card : ℝ)
            / Fintype.card Y := by
      intro a
      rw [normTrace, trace_readout_mul, div_natCast_re _ hne]
      simp
    simp only [hterm, ← Finset.sum_div]
    rw [← Nat.cast_sum, sum_agree_card]
  have hsplit :
      ((Finset.univ.filter fun y ↦ f y = g y).card : ℝ)
        + ((Finset.univ.filter fun y ↦ f y ≠ g y).card : ℝ)
        = (Fintype.card Y : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not,
      Fintype.card]
  rw [consDefect, hone, hmatch]
  field_simp
  linarith

end Readout

end ConsistencyDistance

end GroupApproximation
