import GroupApproximation.Sofic.HyperlinearAmplification
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Positivity

/-!
# The norm–trace interface: operator-norm approximation carries no trace

Hyperlinearity is approximation in the *normalized Hilbert–Schmidt* metric.
The operator-norm world — matricial approximation of the kind studied under
weak-MF and strong-convergence headings — looks adjacent, and a route to a
negative answer to Question 3.4 has been proposed through it: find a nonsofic
group, prove it operator-norm approximable, conclude hyperlinear.  This file
formalizes the exact interface between the two metrics, and both halves of it
are one-sided in the same direction.

* **The domination** (`hsDistSq_le_sq_l2_opNorm`): the squared normalized
  Hilbert–Schmidt distance is at most the squared operator-norm distance,
  *independently of dimension*.  So operator-norm multiplicativity defects
  transfer to Hilbert–Schmidt defects for free, on any model of any size.

* **The bridge** (`NormModel.toHyperlinearModel`): consequently an
  operator-norm model becomes a hyperlinear model the moment its normalized
  traces separate.  The trace clause is the *entire* active hypothesis: the
  norm clause supplies multiplicativity and nothing else.

* **The gap** (`NormModel.exists_hs_collapse`): the trace clause is not free.
  Padding a model with an identity block of vanishing relative dimension
  preserves every operator-norm distance exactly
  (`l2_opNorm_cornerPad`) while collapsing every Hilbert–Schmidt
  distance below any prescribed bound.  Operator-norm approximation can be one
  hundred percent trace-invisible, so no implication from norm approximability
  to hyperlinearity exists at the level of models, and the proposed route is
  closed at its second arrow unless a trace hypothesis is supplied separately.

* **The tradeoff, corrected** (`norm_normTrace_sub_one_le`,
  `phase_deviation_no_amplification`, `norm_normTrace_tensorPow`): deviation
  supported on a corner of vanishing density forces the normalized trace to
  `1`, so exact or corner-supported data cannot trace-separate — that is the
  padding phenomenon restated pointwise.  But the support of `u - 1` is the
  *wrong* invariant for the converse: `i·1` has invertible deviation — full
  support, full rank — and every tensor power of it has normalized trace of
  modulus one.  The invariant amplification actually drives is
  `1 - ‖normTrace u‖`, the distance to the scalars: the normalized trace is
  exactly multiplicative under tensor powers, so separation amplifies at an
  exponential rate precisely on the non-scalar part.  This is the scalar-phase
  obstruction of `tensorPow_phase_collapse` recurring on the trace side.

What this file does **not** prove, and does not claim: that any group is or is
not operator-norm approximable; any spectral-gap correction of almost
representations; any simplicity statement for the nonsofic witness.  Those are
the open or unformalized parts of the proposed route, and they are quoted
nowhere in this development.
-/

namespace GroupApproximation

open Matrix
open scoped Matrix.Norms.L2Operator

/-! ## The Euclidean toolkit

Three bridge lemmas between the entrywise `normSq` sums this development
computes with and Mathlib's `L2` operator norm on matrices.  Everything later
goes through these; no other statement mentions `EuclideanSpace`.
-/

/-- The squared Euclidean norm of a vector is its entrywise `normSq` sum. -/
theorem euclidean_norm_sq (Y : FiniteModel) (w : Y → ℂ) :
    ‖(EuclideanSpace.equiv Y ℂ).symm w‖ ^ 2 = ∑ i : Y, Complex.normSq (w i) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  exact Finset.sum_congr rfl fun i _ ↦ (Complex.normSq_eq_norm_sq _).symm

/-- The operator norm bounds every matrix–vector product, in `normSq` form. -/
theorem sum_normSq_mulVec_le (Y : FiniteModel) (C : Matrix Y Y ℂ) (x : Y → ℂ) :
    ∑ i : Y, Complex.normSq ((C *ᵥ x) i)
      ≤ ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) := by
  have h : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖
      ≤ ‖C‖ * ‖(EuclideanSpace.equiv Y ℂ).symm x‖ :=
    Matrix.l2_opNorm_mulVec C ((EuclideanSpace.equiv Y ℂ).symm x)
  have hL := euclidean_norm_sq Y (C *ᵥ x)
  have hR := euclidean_norm_sq Y x
  have hsq : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2
      ≤ (‖C‖ * ‖(EuclideanSpace.equiv Y ℂ).symm x‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ :=
      norm_nonneg _
    nlinarith only [h, h0, norm_nonneg ((EuclideanSpace.equiv Y ℂ).symm x),
      norm_nonneg C]
  calc ∑ i : Y, Complex.normSq ((C *ᵥ x) i)
      = ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2 := hL.symm
    _ ≤ (‖C‖ * ‖(EuclideanSpace.equiv Y ℂ).symm x‖) ^ 2 := hsq
    _ = ‖C‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) := by rw [mul_pow, hR]

/-- The converse criterion: a uniform `normSq` bound on matrix–vector products
bounds the operator norm. -/
theorem l2_opNorm_le_of_sum_normSq (Y : FiniteModel) (C : Matrix Y Y ℂ)
    {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ x : Y → ℂ, ∑ i : Y, Complex.normSq ((C *ᵥ x) i)
      ≤ M ^ 2 * ∑ i : Y, Complex.normSq (x i)) :
    ‖C‖ ≤ M := by
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x ↦ ?_
  have hL : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2
      = ∑ i : Y, Complex.normSq ((C *ᵥ x) i) := euclidean_norm_sq Y _
  have hR : ‖(EuclideanSpace.equiv Y ℂ).symm x‖ ^ 2
      = ∑ i : Y, Complex.normSq (x i) := euclidean_norm_sq Y x
  have hval : ‖(LinearEquiv.trans (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Y) (n := Y))
      LinearMap.toContinuousLinearMap C) x‖
      = ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ := rfl
  rw [hval]
  have hx : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [hL, mul_pow]
    have hxx : ‖x‖ ^ 2 = ∑ i : Y, Complex.normSq (x i) := hR
    rw [hxx]
    exact h x
  have h1 : ‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖
      = Real.sqrt (‖(EuclideanSpace.equiv Y ℂ).symm (C *ᵥ x)‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  have h2 : Real.sqrt ((M * ‖x‖) ^ 2) = M * ‖x‖ :=
    Real.sqrt_sq (mul_nonneg hM (norm_nonneg _))
  rw [h1, ← h2]
  exact Real.sqrt_le_sqrt hx

/-! ## The domination: Hilbert–Schmidt below operator norm, at every size -/

/-- **Operator-norm defects dominate normalized Hilbert–Schmidt defects,
independently of dimension.**  Column by column: each column of `C` is a
matrix–vector product against a basis vector, so its mass is at most `‖C‖²`,
and the normalization divides by exactly the number of columns. -/
theorem hsDistSq_le_sq_l2_opNorm (Y : FiniteModel) (A B : Matrix Y Y ℂ) :
    hsDistSq Y A B ≤ ‖A - B‖ ^ 2 := by
  classical
  set C := A - B with hC
  have hcol : ∀ j : Y, ∑ i : Y, Complex.normSq (C i j) ≤ ‖C‖ ^ 2 := by
    intro j
    have h := sum_normSq_mulVec_le Y C (Pi.single j 1)
    have hx : ∑ k : Y, Complex.normSq ((Pi.single j (1 : ℂ) : Y → ℂ) k) = 1 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        simp [hb]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    have hcolv : ∀ k : Y, (C *ᵥ Pi.single j (1 : ℂ)) k = C k j := by
      intro k
      rw [Matrix.mulVec_single_one]
      rfl
    rw [hx, mul_one] at h
    calc ∑ i : Y, Complex.normSq (C i j)
        = ∑ i : Y, Complex.normSq ((C *ᵥ Pi.single j (1 : ℂ)) i) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [hcolv i]
      _ ≤ ‖C‖ ^ 2 := h
  have hsum : ∑ i : Y, ∑ j : Y, Complex.normSq (C i j)
      ≤ (Fintype.card Y : ℝ) * ‖C‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc ∑ j : Y, ∑ i : Y, Complex.normSq (C i j)
        ≤ ∑ _j : Y, ‖C‖ ^ 2 := Finset.sum_le_sum fun j _ ↦ hcol j
      _ = (Fintype.card Y : ℝ) * ‖C‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  show (∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)) / Fintype.card Y
      ≤ ‖A - B‖ ^ 2
  by_cases hY : Fintype.card Y = 0
  · rw [hY]
    simp only [Nat.cast_zero, div_zero]
    positivity
  · have hYpos : (0 : ℝ) < Fintype.card Y := by
      exact_mod_cast Nat.pos_of_ne_zero hY
    rw [div_le_iff₀ hYpos]
    calc ∑ i : Y, ∑ j : Y, Complex.normSq (A i j - B i j)
        ≤ (Fintype.card Y : ℝ) * ‖C‖ ^ 2 := hsum
      _ = ‖A - B‖ ^ 2 * (Fintype.card Y : ℝ) := by rw [hC]; ring

/-! ## Operator-norm models

The operator-norm analogue of `HyperlinearModel`: unitary matrices,
multiplicativity and separation both measured in operator norm, in the same
local finite-test-set format as the other models in this development.  `δ` is
the separation constant and `ε` the multiplicative accuracy; the separation
is pinned at a constant because the operator norm, unlike the
Hilbert–Schmidt norm on unitaries, has no canonical maximal separation to
normalize to.
-/

/-! ## The bridge: the trace clause is the entire active hypothesis -/

/-! ## The corner padding

The block-diagonal extension of a model by an identity block.  It preserves
units, products, adjoints, and — the point — every operator-norm distance
exactly, while diluting every Hilbert–Schmidt quantity by the relative
dimension of the original block.
-/

/-! ## Trace bounds for unitaries -/

/-! ## The corner-hiding theorem: norm data is trace-invisible

Padding preserves the operator-norm structure of a model exactly and dilutes
its Hilbert–Schmidt geometry to nothing.  So operator-norm approximability
places no constraint whatever on the Hilbert–Schmidt side: the trace clause of
the bridge is not a convenience but the entire content, and no argument from
norm approximation to hyperlinearity can avoid supplying it separately.
-/

/-! ## Corner-supported deviation cannot trace-separate -/

/-! ## Amplification drives distance to the scalars, not deviation rank -/

end GroupApproximation
