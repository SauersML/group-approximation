import GroupApproximation.Analysis.KirchbergRordamEpsilonTest
import GroupApproximation.Analysis.NormMatrixCorona

/-!
# Countable saturation of the matrix corona

The Kirchberg--Rørdam corona theory used by Tikuisis--White--Winter rests on
one structural feature of `Q = ∏ Mₖ / ⊕ Mₖ`: a countable list of requirements,
each of which can be met *approximately* by a sequence of matrices, can be met
*exactly* by a single element of the corona.  In their language the corona is
countably degree-`1` saturated; the mechanism is Kirchberg's `ε`-test, which
`Analysis.KirchbergRordamEpsilonTest` proves.

This file transports the `ε`-test to the corona built in
`Analysis.NormMatrixCorona`, and it is entirely unconditional.

## The three statements

* `corona_mk_eq_zero_of_tendsto` --- a bounded matrix sequence whose
  coordinate norms tend to zero is *zero* in the corona.  This is the
  translation device: "the defect vanishes in the limit" and "the defect is
  literally `0` in `Q`" are the same statement.
* `exists_seq_tendsto_of_approximate` --- **the saturation theorem**.  Given
  countably many nonnegative defect functions on contractions, if every finite
  subfamily can be made eventually smaller than every `ε` by *some* sequence
  of contractions, then a single sequence of contractions drives *all* of them
  to zero.
* `exists_corona_solution` --- the same, read in the corona: the requirements
  are met exactly, by one element.

## Why contractions

The `ε`-test produces a point of a product `∀ n, Xₙ`; for the result to name
an element of the corona the coordinates must be uniformly bounded, and an
arbitrary product of matrix algebras is not.  Restricting the search space to
the unit ball is not a loss --- every requirement in the quasidiagonality
argument is a requirement on contractions --- and it is what makes the
diagonal sequence a member of `ℓ∞`.

## What this file does not do

Countable saturation is one of two things TWW takes from Kirchberg--Rørdam.
The other is the lifting theory for order-zero maps into a corona (`Q` is a
`σ`-ideal in `∏ Mₖ`, so c.p.c. order-zero maps into `Q` lift to sequences of
c.p.c. order-zero maps).  That is a genuinely analytic theorem about the cone
`C₀((0,1]) ⊗ A` being projective, and it is not proved here; it is recorded
with attribution in `Analysis.KirchbergRordamOrderZeroLift`.
-/

namespace GroupApproximation
namespace KirchbergRordam

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable (X : ℕ → Type u) [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
  [∀ n, Nonempty (X n)]

noncomputable section

/-! ## Vanishing in the corona -/

/-- **Vanishing in the corona is vanishing in the limit.**  The cofinite
filter on `ℕ` is `atTop`, so a sequence of matrices whose norms tend to zero
represents `0` in `ℓ∞/c₀`. -/
theorem corona_mk_eq_zero_of_tendsto (b : BoundedMatrixSequence X)
    (hb : Tendsto (fun n => ‖b n‖) atTop (nhds 0)) :
    normMatrixCStarCoronaMk X b = 0 := by
  rw [normMatrixCStarCoronaMk_eq_zero_iff]
  show Tendsto (fun n => ‖b n‖) cofinite (nhds 0)
  rw [Nat.cofinite_eq_atTop]
  exact hb

/-! ## The search space: sequences of contractions -/

/-- The unit ball of the `n`-th matrix algebra, as a type.  The `ε`-test
searches a product of *sets*, and this is the set the corona applications
search. -/
abbrev MatrixContraction (n : ℕ) : Type u :=
  {M : Matrix (X n) (X n) ℂ // ‖M‖ ≤ 1}

/-- A sequence of contractions is a bounded matrix sequence. -/
def ofContractionSeq (x : ∀ n, MatrixContraction X n) : BoundedMatrixSequence X :=
  ⟨fun n => (x n).1, memℓp_infty_iff.mpr ⟨1, by
    rintro _ ⟨n, rfl⟩
    exact (x n).2⟩⟩

omit [∀ (n : ℕ), Nonempty (X n)] in
@[simp] theorem ofContractionSeq_apply (x : ∀ n, MatrixContraction X n) (n : ℕ) :
    ofContractionSeq X x n = (x n).1 := rfl

/-! ## Saturation -/

omit [∀ (n : ℕ), Nonempty (X n)] in
/-- **Countable saturation of the matrix corona** (Kirchberg--Rørdam 2014,
via Kirchberg's `ε`-test).

`g k n` is the `k`-th defect, measured at stage `n` on a contraction.  The
hypothesis is that *finitely many defects at a time* can be made *eventually
small*, by a sequence that may depend on how many defects and on how small.
The conclusion is that **one** sequence of contractions sends *every* defect
to zero.

The gap between the two is exactly the gap between "for each `ε` there is a
matrix model" and "there is a sequence of matrix models" --- the step that a
quasidiagonality argument must take to pass from a local statement to a
sequential one. -/
theorem exists_seq_tendsto_of_approximate
    (g : ℕ → ∀ n : ℕ, MatrixContraction X n → ℝ)
    (hg : ∀ (k n : ℕ) (M : MatrixContraction X n), 0 ≤ g k n M)
    (happrox : ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ x : ∀ n, MatrixContraction X n, ∀ k ≤ m,
        ∀ᶠ n in atTop, g k n (x n) < ε) :
    ∃ x : ∀ n, MatrixContraction X n, ∀ k : ℕ,
      Tendsto (fun n => g k n (x n)) atTop (nhds 0) :=
  epsilon_test g hg happrox

/-- **The saturation theorem, read in the corona.**

The defects are now measured by matrix-valued requirement maps `F k`: the
`k`-th requirement is satisfied exactly when the sequence
`n ↦ F k n (x n)` is null, i.e. when it represents `0` in `ℓ∞/c₀`.  If every
finite family of requirements is approximately satisfiable then all of them
are exactly satisfiable, simultaneously, by one sequence of contractions.

The conclusion is phrased through an arbitrary bounded sequence `b`
representing `n ↦ F k n (x n)` rather than by packaging that sequence into
`ℓ∞` inside the statement: the packaging needs a `Memℓp` proof, and carrying
one inside a statement makes the statement depend on which bound was chosen. -/
theorem exists_corona_solution
    (F : ℕ → ∀ n : ℕ, MatrixContraction X n → Matrix (X n) (X n) ℂ)
    (happrox : ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ x : ∀ n, MatrixContraction X n, ∀ k ≤ m,
        ∀ᶠ n in atTop, ‖F k n (x n)‖ < ε) :
    ∃ x : ∀ n, MatrixContraction X n, ∀ (k : ℕ) (b : BoundedMatrixSequence X),
      (∀ n, b n = F k n (x n)) → normMatrixCStarCoronaMk X b = 0 := by
  obtain ⟨x, hx⟩ :=
    exists_seq_tendsto_of_approximate X (fun k n M => ‖F k n M‖)
      (fun k n M => norm_nonneg _) happrox
  refine ⟨x, ?_⟩
  intro k b hb
  refine corona_mk_eq_zero_of_tendsto X b ?_
  have hrw : (fun n => ‖b n‖) = fun n => ‖F k n (x n)‖ := by
    funext n
    rw [hb n]
  rw [hrw]
  exact hx k

/-! ## Multiplicativity in the corona is asymptotic multiplicativity

The corona is where a quasidiagonality statement becomes an *exact* algebraic
statement: a family of matrix models is asymptotically multiplicative exactly
when the induced map into `ℓ∞/c₀` is multiplicative.  `Sofic.MFTraceCoronaBridge`
proves the direction that *builds* the corona homomorphism from a model
(`ShulmanTrace.MFTraceModel.coronaHom`).  The direction below is the other
one, and it is the direction a Tikuisis--White--Winter style argument needs:
the theorem produces a homomorphism into the corona, and what is wanted is the
defect estimate on the representing sequences. -/

/-- **A product identity in the corona is an asymptotic product identity.** -/
theorem tendsto_norm_sub_mul_of_corona_mul {u v w : BoundedMatrixSequence X}
    (h : normMatrixCStarCoronaMk X u * normMatrixCStarCoronaMk X v
      = normMatrixCStarCoronaMk X w) :
    Tendsto (fun n => ‖w n - u n * v n‖) atTop (nhds 0) := by
  have h0 : normMatrixCStarCoronaMk X (w - u * v) = 0 := by
    rw [map_sub, map_mul, h, sub_self]
  rw [normMatrixCStarCoronaMk_eq_zero_iff] at h0
  have hcof : Tendsto (fun n => ‖(w - u * v) n‖) cofinite (nhds 0) := h0
  rw [Nat.cofinite_eq_atTop] at hcof
  refine hcof.congr fun n => ?_
  rw [lp.coeFn_sub, Pi.sub_apply, lp.infty_coeFn_mul, Pi.mul_apply]

/-- **A difference that vanishes in the corona vanishes asymptotically.**  The
form in which an approximate-unitary-equivalence conclusion, which is what
Dadarlat--Eilers supplies, is read back on representing sequences. -/
theorem tendsto_norm_sub_of_corona_eq {u v : BoundedMatrixSequence X}
    (h : normMatrixCStarCoronaMk X u = normMatrixCStarCoronaMk X v) :
    Tendsto (fun n => ‖u n - v n‖) atTop (nhds 0) := by
  have h0 : normMatrixCStarCoronaMk X (u - v) = 0 := by
    rw [map_sub, h, sub_self]
  rw [normMatrixCStarCoronaMk_eq_zero_iff] at h0
  have hcof : Tendsto (fun n => ‖(u - v) n‖) cofinite (nhds 0) := h0
  rw [Nat.cofinite_eq_atTop] at hcof
  refine hcof.congr fun n => ?_
  rw [lp.coeFn_sub, Pi.sub_apply]

end

end KirchbergRordam
end GroupApproximation
