import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Analysis.TracialMatrixUltraproduct

/-!
# What a quasidiagonal trace is, proved rather than assumed

`Quasidiagonal.QuasidiagonalTraceModel` transcribes the conclusion of
Tikuisis--White--Winter literally: a sequence of unital completely positive
matrix models whose multiplicative and trace defects vanish.  The functional
`τ` enters that structure as a bare function `A → ℂ`; **no clause of it
says that `τ` is linear, tracial, positive or unital.**

That is deliberate --- it keeps the transcription checkable against the paper
--- but it leaves an obligation.  If the transcription were wrong, the defect
would show up exactly here: a `τ` satisfying the five clauses would fail to be
a trace.  This file discharges that obligation.  Everything below is proved
from the clauses, with **no** input, no citation, and no appeal to
`Quasidiagonal.UCPContractive`:

* `map_add_of_isQuasidiagonalTrace`, `map_smul_of_isQuasidiagonalTrace` --- `τ`
  is `ℂ`-linear;
* `map_mul_comm_of_isQuasidiagonalTrace` --- `τ(xy) = τ(yx)`;
* `map_star_mul_self_nonneg_of_isQuasidiagonalTrace` --- `0 ≤ τ(x⋆x)`;
* `map_one_of_isQuasidiagonalTrace` --- `τ(1) = 1`, **provided the models are
  nonempty**;
* `QuasidiagonalTraceModel.toTracialState` --- the four together, as a
  `TracialState` in the repository's own sense.

Each is a limit argument against the trace clause.  The only new estimate is
`norm_normTrace_sub_le`, and the only new positivity fact is
`normTrace_nonneg_of_isCompletelyPositive`, which reads the
complete-positivity clause at the `|Y|` single `δ`-vectors and sums.

## The nonemptiness caveat is real, not a technicality

`QuasidiagonalTraceModel` does not ask `0 < kₙ`, and `M_0(ℂ)` is the zero
ring, in which `1 = 0`.  So the **zero functional is a quasidiagonal trace**,
witnessed by empty models --- `isQuasidiagonalTrace_zero` below proves it.
Unitality therefore cannot be a theorem without the nonemptiness hypothesis,
and `toTracialState` carries it.  `ShulmanTrace.MFTraceModel` records the same
phenomenon (`exists_shift`), and the omission is faithful to the source in
both cases: whatever *supplies* the models supplies nonempty ones.

## A positive control at a genuine C⋆-algebra

`Sofic.TikuisisWhiteWinterSites` proves *negative* statements --- that the
canonical trace of one particular reduced group C⋆-algebra is **not**
quasidiagonal.  A negative statement about an unsatisfiable predicate is true
and empty, and no kernel check separates the two.  So the predicate needs an
inhabitant at an algebra that is not the zero ring:
`isQuasidiagonalTrace_complex` is the identity trace on `ℂ`, modelled by the
scalar matrices, with every defect identically zero.

This is not a formality either.  `ℂ` is separable, nuclear, satisfies the UCT,
and its identity trace is faithful, so this is a genuine instance of the
Tikuisis--White--Winter theorem --- the smallest one, and the base case any
proof of the general statement has to reproduce.  It is proved here
unconditionally.  Nothing in this file proves, or contributes to
proving, the theorem at any infinite-dimensional algebra.
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

noncomputable section

universe u v

variable {A : Type u} [CStarAlgebra A]

/-! ## Two elementary tools -/

/-- Permuting a triple sum so that the innermost index becomes the outermost.
Used twice below, once on `(i, j, z)` and once on `(x, y, z)`. -/
theorem sum_comm₃ {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (f : ι → κ → ν → ℂ) :
    (∑ i : ι, ∑ j : κ, ∑ z : ν, f i j z)
      = ∑ z : ν, ∑ i : ι, ∑ j : κ, f i j z := by
  have h1 : ∀ i : ι, (∑ j : κ, ∑ z : ν, f i j z) = ∑ z : ν, ∑ j : κ, f i j z :=
    fun _ ↦ Finset.sum_comm
  simp_rw [h1]
  exact Finset.sum_comm

/-- **The normalized trace moves distances no further apart than the operator
norm does.**  One line from `normTrace_sub` and the printed inequality
`|tr_r(x)| ≤ ‖x‖`; it is the estimate every clause below uses to replace a
trace difference by a matrix difference. -/
theorem norm_normTrace_sub_le (Y : FiniteModel) (P Q : Matrix Y Y ℂ) :
    ‖normTrace Y P - normTrace Y Q‖ ≤ ‖P - Q‖ := by
  rw [← normTrace_sub]
  exact PrintedPreliminaryEstimates.norm_normTrace_le_l2_opNorm Y (P - Q)

/-- A nonnegative constant dominated by a null sequence is zero.  The shape
every clause below closes with. -/
theorem eq_zero_of_le_tendsto_zero {c : ℝ} {g : ℕ → ℝ} (hc : 0 ≤ c)
    (hg : Tendsto g atTop (nhds 0)) (h : ∀ n, c ≤ g n) : c = 0 :=
  le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hg h) hc

/-! ## Positivity of the normalized trace on a completely positive image -/

/-- **A completely positive map sends `x⋆x` to a matrix of nonnegative
normalized trace.**

The complete-positivity clause at the one-element tuple `(x)` and the vector
`δ_y` says exactly that the diagonal entry `φ(x⋆x) y y` is a nonnegative real
(`form_diracVec` identifies the form at a pair of `δ`-vectors with the matrix
entry).  Summing over `y` gives the trace, and dividing by `|Y|` keeps it
nonnegative.

The route through real parts mirrors
`ShulmanTrace.normTrace_star_mul_self_nonneg`, which proves the same
conclusion for a matrix that is *literally* of the form `x⋆x`; that theorem
does not apply here, because `φ(x⋆x)` is positive only by hypothesis on `φ`
and is not presented as a square. -/
theorem normTrace_nonneg_of_isCompletelyPositive {Y : FiniteModel}
    {φ : A → Matrix Y Y ℂ} (hcp : IsCompletelyPositiveOnMatrices Y φ) (x : A) :
    0 ≤ normTrace Y (φ (star x * x)) := by
  have hentry : ∀ y : Y, (0 : ℂ) ≤ φ (star x * x) y y := by
    intro y
    have hre := hcp.form_nonneg x (diracVec Y y)
    have him := hcp.form_im x (diracVec Y y)
    rw [form_diracVec Y (φ (star x * x)) y y] at hre him
    exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩
  have htrace : (0 : ℂ) ≤ Matrix.trace (φ (star x * x)) := by
    simp only [Matrix.trace, Matrix.diag]
    exact Finset.sum_nonneg fun y _ ↦ hentry y
  have hre : (0 : ℝ) ≤ (Matrix.trace (φ (star x * x))).re :=
    (Complex.nonneg_iff.mp htrace).1
  have heq : Matrix.trace (φ (star x * x))
      = (((Matrix.trace (φ (star x * x))).re : ℝ) : ℂ) :=
    Complex.eq_re_of_ofReal_le (by rw [Complex.ofReal_zero]; exact htrace)
  rw [normTrace, heq, ← Complex.ofReal_natCast (Fintype.card Y),
    ← Complex.ofReal_div]
  exact Complex.zero_le_real.mpr (div_nonneg hre (by positivity))

/-! ## A quasidiagonal trace is linear -/

/-- **Additivity.**  `τ(x + y) − τ(x) − τ(y)` is dominated by the three trace
defects at `x + y`, `x` and `y`, because each `φₙ` is exactly linear and the
normalized trace is exactly additive. -/
theorem map_add_of_isQuasidiagonalTrace {τ : A → ℂ}
    (h : IsQuasidiagonalTrace τ) (x y : A) : τ (x + y) = τ x + τ y := by
  obtain ⟨M⟩ := h
  have hlim : Tendsto (fun n ↦
      ‖τ (x + y) - normTrace (M.space n) (M.map n (x + y))‖
        + ‖τ x - normTrace (M.space n) (M.map n x)‖
        + ‖τ y - normTrace (M.space n) (M.map n y)‖) atTop (nhds 0) := by
    simpa using ((M.tendsto_trace (x + y)).add (M.tendsto_trace x)).add
      (M.tendsto_trace y)
  have hbound : ∀ n, ‖τ (x + y) - τ x - τ y‖
      ≤ ‖τ (x + y) - normTrace (M.space n) (M.map n (x + y))‖
        + ‖τ x - normTrace (M.space n) (M.map n x)‖
        + ‖τ y - normTrace (M.space n) (M.map n y)‖ := by
    intro n
    have hlin : normTrace (M.space n) (M.map n (x + y))
        = normTrace (M.space n) (M.map n x) + normTrace (M.space n) (M.map n y) := by
      rw [map_add]
      exact TracialUltraproduct.normTrace_add _ _ _
    have e : τ (x + y) - τ x - τ y
        = (τ (x + y) - normTrace (M.space n) (M.map n (x + y)))
          - (τ x - normTrace (M.space n) (M.map n x))
          - (τ y - normTrace (M.space n) (M.map n y)) := by
      rw [hlin]; ring
    rw [e]
    have h1 := norm_sub_le
      ((τ (x + y) - normTrace (M.space n) (M.map n (x + y)))
        - (τ x - normTrace (M.space n) (M.map n x)))
      (τ y - normTrace (M.space n) (M.map n y))
    have h2 := norm_sub_le
      (τ (x + y) - normTrace (M.space n) (M.map n (x + y)))
      (τ x - normTrace (M.space n) (M.map n x))
    linarith
  have h0 : ‖τ (x + y) - τ x - τ y‖ = 0 :=
    eq_zero_of_le_tendsto_zero (norm_nonneg _) hlim hbound
  have := norm_eq_zero.mp h0
  linear_combination this

/-- **Homogeneity.**  The same argument at `c • x`, using that `φₙ` is exactly
`ℂ`-linear and that the normalized trace is exactly homogeneous. -/
theorem map_smul_of_isQuasidiagonalTrace {τ : A → ℂ}
    (h : IsQuasidiagonalTrace τ) (c : ℂ) (x : A) : τ (c • x) = c * τ x := by
  obtain ⟨M⟩ := h
  have hlim : Tendsto (fun n ↦
      ‖τ (c • x) - normTrace (M.space n) (M.map n (c • x))‖
        + ‖c‖ * ‖τ x - normTrace (M.space n) (M.map n x)‖) atTop (nhds 0) := by
    simpa using (M.tendsto_trace (c • x)).add
      ((M.tendsto_trace x).const_mul ‖c‖)
  have hbound : ∀ n, ‖τ (c • x) - c * τ x‖
      ≤ ‖τ (c • x) - normTrace (M.space n) (M.map n (c • x))‖
        + ‖c‖ * ‖τ x - normTrace (M.space n) (M.map n x)‖ := by
    intro n
    have hlin : normTrace (M.space n) (M.map n (c • x))
        = c * normTrace (M.space n) (M.map n x) := by
      rw [map_smul]
      exact TracialUltraproduct.normTrace_smul _ c _
    have e : τ (c • x) - c * τ x
        = (τ (c • x) - normTrace (M.space n) (M.map n (c • x)))
          - c * (τ x - normTrace (M.space n) (M.map n x)) := by
      rw [hlin]; ring
    rw [e]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [norm_mul]
  have h0 : ‖τ (c • x) - c * τ x‖ = 0 :=
    eq_zero_of_le_tendsto_zero (norm_nonneg _) hlim hbound
  have := norm_eq_zero.mp h0
  linear_combination this

/-! ## A quasidiagonal trace is tracial -/

/-- **`τ(xy) = τ(yx)`.**  The five-term telescope

```text
τ(xy) − τ(yx) = (τ(xy) − tr φₙ(xy)) + (tr φₙ(xy) − tr(φₙx·φₙy))
                 + (tr(φₙx·φₙy) − tr(φₙy·φₙx))
                 + (tr(φₙy·φₙx) − tr φₙ(yx)) + (tr φₙ(yx) − τ(yx)),
```

whose middle term is **exactly zero** by cyclicity of the matrix trace, and
whose other four are the trace and multiplicativity defects.  This is the
clause that makes the transcription a statement about *traces*: nothing in
`QuasidiagonalTraceModel` says so, and it is true anyway. -/
theorem map_mul_comm_of_isQuasidiagonalTrace {τ : A → ℂ}
    (h : IsQuasidiagonalTrace τ) (x y : A) : τ (x * y) = τ (y * x) := by
  obtain ⟨M⟩ := h
  have hlim : Tendsto (fun n ↦
      ‖τ (x * y) - normTrace (M.space n) (M.map n (x * y))‖
        + ‖M.map n (x * y) - M.map n x * M.map n y‖
        + ‖M.map n (y * x) - M.map n y * M.map n x‖
        + ‖τ (y * x) - normTrace (M.space n) (M.map n (y * x))‖)
      atTop (nhds 0) := by
    simpa using (((M.tendsto_trace (x * y)).add (M.tendsto_mul x y)).add
      (M.tendsto_mul y x)).add (M.tendsto_trace (y * x))
  have hbound : ∀ n, ‖τ (x * y) - τ (y * x)‖
      ≤ ‖τ (x * y) - normTrace (M.space n) (M.map n (x * y))‖
        + ‖M.map n (x * y) - M.map n x * M.map n y‖
        + ‖M.map n (y * x) - M.map n y * M.map n x‖
        + ‖τ (y * x) - normTrace (M.space n) (M.map n (y * x))‖ := by
    intro n
    have hcyc : normTrace (M.space n) (M.map n x * M.map n y)
        = normTrace (M.space n) (M.map n y * M.map n x) :=
      TracialUltraproduct.normTrace_mul_comm _ _ _
    have e : τ (x * y) - τ (y * x)
        = (τ (x * y) - normTrace (M.space n) (M.map n (x * y)))
          + (normTrace (M.space n) (M.map n (x * y))
              - normTrace (M.space n) (M.map n x * M.map n y))
          - (normTrace (M.space n) (M.map n (y * x))
              - normTrace (M.space n) (M.map n y * M.map n x))
          - (τ (y * x) - normTrace (M.space n) (M.map n (y * x))) := by
      rw [hcyc]; ring
    have b2 : ‖normTrace (M.space n) (M.map n (x * y))
        - normTrace (M.space n) (M.map n x * M.map n y)‖
        ≤ ‖M.map n (x * y) - M.map n x * M.map n y‖ :=
      norm_normTrace_sub_le _ _ _
    have b3 : ‖normTrace (M.space n) (M.map n (y * x))
        - normTrace (M.space n) (M.map n y * M.map n x)‖
        ≤ ‖M.map n (y * x) - M.map n y * M.map n x‖ :=
      norm_normTrace_sub_le _ _ _
    rw [e]
    have s1 := norm_sub_le
      ((τ (x * y) - normTrace (M.space n) (M.map n (x * y)))
        + (normTrace (M.space n) (M.map n (x * y))
            - normTrace (M.space n) (M.map n x * M.map n y))
        - (normTrace (M.space n) (M.map n (y * x))
            - normTrace (M.space n) (M.map n y * M.map n x)))
      (τ (y * x) - normTrace (M.space n) (M.map n (y * x)))
    have s2 := norm_sub_le
      ((τ (x * y) - normTrace (M.space n) (M.map n (x * y)))
        + (normTrace (M.space n) (M.map n (x * y))
            - normTrace (M.space n) (M.map n x * M.map n y)))
      (normTrace (M.space n) (M.map n (y * x))
        - normTrace (M.space n) (M.map n y * M.map n x))
    have s3 := norm_add_le
      (τ (x * y) - normTrace (M.space n) (M.map n (x * y)))
      (normTrace (M.space n) (M.map n (x * y))
        - normTrace (M.space n) (M.map n x * M.map n y))
    linarith [s1, s2, s3, b2, b3]
  have h0 : ‖τ (x * y) - τ (y * x)‖ = 0 :=
    eq_zero_of_le_tendsto_zero (norm_nonneg _) hlim hbound
  have := norm_eq_zero.mp h0
  linear_combination this

/-! ## A quasidiagonal trace is positive -/

/-- **`0 ≤ τ(x⋆x)`.**  Each `tr φₙ(x⋆x)` is a nonnegative real by
`normTrace_nonneg_of_isCompletelyPositive`, and `τ(x⋆x)` is its limit: the
imaginary part is dominated by the trace defect and the real part is bounded
below by minus it.

This is the clause that uses complete positivity.  The other three use only
linearity, unitality and the trace defect. -/
theorem map_star_mul_self_nonneg_of_isQuasidiagonalTrace {τ : A → ℂ}
    (h : IsQuasidiagonalTrace τ) (x : A) : 0 ≤ τ (star x * x) := by
  obtain ⟨M⟩ := h
  have hpos : ∀ n, (0 : ℂ) ≤ normTrace (M.space n) (M.map n (star x * x)) :=
    fun n ↦ normTrace_nonneg_of_isCompletelyPositive (M.completelyPositive n) x
  have hdef := M.tendsto_trace (star x * x)
  have him : (τ (star x * x)).im = 0 := by
    have hb : ∀ n, |(τ (star x * x)).im|
        ≤ ‖τ (star x * x) - normTrace (M.space n) (M.map n (star x * x))‖ := by
      intro n
      have h0 : (normTrace (M.space n) (M.map n (star x * x))).im = 0 :=
        ((Complex.nonneg_iff.mp (hpos n)).2).symm
      have e : (τ (star x * x)).im
          = (τ (star x * x)
              - normTrace (M.space n) (M.map n (star x * x))).im := by
        rw [Complex.sub_im, h0, sub_zero]
      rw [e]
      exact Complex.abs_im_le_norm _
    have := eq_zero_of_le_tendsto_zero (abs_nonneg _) hdef hb
    exact abs_eq_zero.mp this
  have hre : 0 ≤ (τ (star x * x)).re := by
    have hb : ∀ n, -(τ (star x * x)).re
        ≤ ‖τ (star x * x) - normTrace (M.space n) (M.map n (star x * x))‖ := by
      intro n
      have h0 : 0 ≤ (normTrace (M.space n) (M.map n (star x * x))).re :=
        (Complex.nonneg_iff.mp (hpos n)).1
      have e : (normTrace (M.space n) (M.map n (star x * x))
          - τ (star x * x)).re
          = (normTrace (M.space n) (M.map n (star x * x))).re
            - (τ (star x * x)).re := Complex.sub_re _ _
      have hle : (normTrace (M.space n) (M.map n (star x * x))
          - τ (star x * x)).re
          ≤ ‖normTrace (M.space n) (M.map n (star x * x)) - τ (star x * x)‖ :=
        (le_abs_self _).trans (Complex.abs_re_le_norm _)
      rw [norm_sub_rev] at hle
      linarith [hle, h0, e.ge, e.le]
    have := le_of_tendsto_of_tendsto' tendsto_const_nhds hdef hb
    linarith
  exact Complex.nonneg_iff.mpr ⟨hre, him.symm⟩

/-! ## Unitality, and why it needs the models to be nonempty -/

/-- **`τ(1) = 1` when the models are nonempty.**  `φₙ(1) = 1` is a clause of
the structure and `tr_r(1) = 1` needs `kₙ > 0`; the trace defect at `1` is then
the constant `‖τ(1) − 1‖`. -/
theorem map_one_of_isQuasidiagonalTrace {τ : A → ℂ}
    (M : QuasidiagonalTraceModel τ)
    (hne : ∀ n, 0 < Fintype.card (M.space n)) : τ 1 = 1 := by
  have hconst : ∀ n, ‖τ 1 - (1 : ℂ)‖
      ≤ ‖τ 1 - normTrace (M.space n) (M.map n 1)‖ := by
    intro n
    rw [M.map_one n, normTrace_one' _ (hne n)]
  have h0 : ‖τ 1 - (1 : ℂ)‖ = 0 :=
    eq_zero_of_le_tendsto_zero (norm_nonneg _) (M.tendsto_trace 1) hconst
  have := norm_eq_zero.mp h0
  linear_combination this

/-- **The zero functional is a quasidiagonal trace**, witnessed by empty
models.  `M_0(ℂ)` is the zero ring, so `φ(1) = 1` holds there for the wrong
reason, every norm is `0`, and `tr_r` of anything is `0/0 = 0`.

This is why `map_one_of_isQuasidiagonalTrace` has a nonemptiness hypothesis
and why `toTracialState` carries one.  It is a fact about the transcription,
not a defect in it: Tikuisis--White--Winter produce nonempty models, and
demanding nonemptiness here would assume more than the theorem gives. -/
theorem isQuasidiagonalTrace_zero : IsQuasidiagonalTrace (fun _ : A ↦ (0 : ℂ)) := by
  classical
  exact ⟨{ space := fun _ ↦ ⟨Empty, inferInstance, inferInstance⟩
           map := fun _ ↦ 0
           map_one := fun _ ↦ by
             ext p q
             exact p.elim
           completelyPositive := fun _ ↦ by
             intro m a w
             constructor <;> simp
           tendsto_mul := fun a b ↦
             ShulmanTrace.tendsto_zero_of_eq_zero fun _ ↦ by simp
           tendsto_trace := fun a ↦
             ShulmanTrace.tendsto_zero_of_eq_zero fun _ ↦ by
               simp [TracialUltraproduct.normTrace_zero] }⟩

/-- **A quasidiagonal trace with nonempty models is a tracial state**, in the
repository's own `TracialState` sense: a unital, positive, tracial linear
functional.

Every field is a theorem above.  Nothing here is assumed, and in particular
this does **not** use `Quasidiagonal.UCPContractive`: contractivity of a ucp
map is needed to compare a quasidiagonal trace with Shulman's MF trace, not to
see that it is a trace. -/
def QuasidiagonalTraceModel.toTracialState {τ : A → ℂ}
    (M : QuasidiagonalTraceModel τ)
    (hne : ∀ n, 0 < Fintype.card (M.space n)) : TracialState A where
  toLinearMap :=
    { toFun := τ
      map_add' := map_add_of_isQuasidiagonalTrace ⟨M⟩
      map_smul' := fun c x ↦ map_smul_of_isQuasidiagonalTrace ⟨M⟩ c x }
  map_one := map_one_of_isQuasidiagonalTrace M hne
  map_star_mul_self_nonneg :=
    map_star_mul_self_nonneg_of_isQuasidiagonalTrace ⟨M⟩
  map_mul_comm := map_mul_comm_of_isQuasidiagonalTrace ⟨M⟩

/-! ## Pullback along a unital `⋆`-homomorphism -/

variable {B : Type v} [CStarAlgebra B]

/-- **Quasidiagonal traces pull back.**  Composing the models of `τ` with a
unital `⋆`-homomorphism `π : A → B` gives models for `τ ∘ π`.

Stated for a linear map with the three algebraic hypotheses spelled out rather
than for a bundled `A →⋆ₐ[ℂ] B`, so that no clause has to see through the
`StarAlgHom → AlgHom → LinearMap` coercion tower; `compStarAlgHom` is the
bundled corollary.

Each clause is the corresponding clause of `M` read at `π x`: `π` is *exactly*
multiplicative, so the multiplicative defect at `(x, y)` is the defect of `M`
at `(π x, π y)`, and `π` is exactly `⋆`-preserving, so the complete-positivity
form at the tuple `a` is the form of `M` at `π ∘ a`.  Nothing needs `π`
injective, surjective or isometric. -/
def QuasidiagonalTraceModel.comp {τ : B → ℂ} (M : QuasidiagonalTraceModel τ)
    (π : A →ₗ[ℂ] B) (hone : π 1 = 1) (hmul : ∀ x y : A, π (x * y) = π x * π y)
    (hstar : ∀ x : A, π (star x) = star (π x)) :
    QuasidiagonalTraceModel (fun x : A ↦ τ (π x)) where
  space := M.space
  map n := (M.map n).comp π
  map_one n := by
    simp only [LinearMap.comp_apply, hone]
    exact M.map_one n
  completelyPositive n := by
    intro m a w
    have hrw : ∀ i j : Fin m, π (star (a i) * a j) = star (π (a i)) * π (a j) :=
      fun i j ↦ by rw [hmul, hstar]
    simpa only [LinearMap.comp_apply, hrw] using
      M.completelyPositive n m (fun i ↦ π (a i)) w
  tendsto_mul x y := by
    simpa only [LinearMap.comp_apply, hmul] using M.tendsto_mul (π x) (π y)
  tendsto_trace x := by
    simpa only [LinearMap.comp_apply] using M.tendsto_trace (π x)

/-- The bundled form of `QuasidiagonalTraceModel.comp`. -/
def QuasidiagonalTraceModel.compStarAlgHom {τ : B → ℂ}
    (M : QuasidiagonalTraceModel τ) (π : A →⋆ₐ[ℂ] B) :
    QuasidiagonalTraceModel (fun x : A ↦ τ (π x)) :=
  M.comp π.toAlgHom.toLinearMap (by simp) (fun x y ↦ by simp)
    (fun x ↦ map_star π x)

/-- The proposition-level pullback. -/
theorem IsQuasidiagonalTrace.comp {τ : B → ℂ} (h : IsQuasidiagonalTrace τ)
    (π : A →⋆ₐ[ℂ] B) : IsQuasidiagonalTrace (fun x : A ↦ τ (π x)) := by
  obtain ⟨M⟩ := h
  exact ⟨M.compStarAlgHom π⟩

/-! ## The positive control: the identity trace on `ℂ` -/

/-- The scalar embedding `ℂ → M_Y(ℂ)`, `z ↦ z · 1`, as a linear map. -/
def scalarModelMap (Y : FiniteModel) : ℂ →ₗ[ℂ] Matrix Y Y ℂ where
  toFun z := Matrix.diagonal fun _ ↦ z
  map_add' z w := by
    ext p q
    by_cases hpq : p = q <;> simp [hpq]
  map_smul' c z := by
    ext p q
    by_cases hpq : p = q <;> simp [hpq]

@[simp] theorem scalarModelMap_apply (Y : FiniteModel) (z : ℂ) :
    scalarModelMap Y z = Matrix.diagonal (fun _ : Y ↦ z) :=
  rfl

@[simp] theorem scalarModelMap_entry (Y : FiniteModel) (z : ℂ) (p q : Y) :
    scalarModelMap Y z p q = if p = q then z else 0 := by
  rw [scalarModelMap_apply, Matrix.diagonal_apply]

theorem scalarModelMap_one (Y : FiniteModel) : scalarModelMap Y 1 = 1 := by
  ext p q
  by_cases hpq : p = q <;> simp [Matrix.one_apply, hpq]

theorem scalarModelMap_mul (Y : FiniteModel) (z w : ℂ) :
    scalarModelMap Y (z * w) = scalarModelMap Y z * scalarModelMap Y w := by
  rw [scalarModelMap_apply, scalarModelMap_apply, scalarModelMap_apply,
    Matrix.diagonal_mul_diagonal]

theorem normTrace_scalarModelMap (Y : FiniteModel) (hY : 0 < Fintype.card Y)
    (z : ℂ) : normTrace Y (scalarModelMap Y z) = z := by
  have hne : ((Fintype.card Y : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hY.ne'
  show Matrix.trace (scalarModelMap Y z) / ((Fintype.card Y : ℕ) : ℂ) = z
  rw [scalarModelMap_apply, Matrix.trace_diagonal, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_comm, mul_div_assoc, div_self hne,
    mul_one]

/-- **The scalar embedding is completely positive.**  For a tuple `z : Fin m → ℂ`
and vectors `w`, the form collapses --- the matrix is diagonal --- to

```text
∑_p |∑_j z_j w_j p|²,
```

a sum of squared moduli.  The two rearrangements are `sum_comm₃` and
`Finset.sum_mul_sum`. -/
theorem isCompletelyPositiveOnMatrices_scalarModelMap (Y : FiniteModel) :
    IsCompletelyPositiveOnMatrices Y ⇑(scalarModelMap Y) := by
  intro m z w
  have hcollapse : ∀ (i j : Fin m) (p : Y),
      (∑ q : Y, (starRingEnd ℂ) (w i p)
          * scalarModelMap Y (star (z i) * z j) p q * w j q)
        = (starRingEnd ℂ) (z i * w i p) * (z j * w j p) := by
    intro i j p
    have hterm : ∀ q : Y, (starRingEnd ℂ) (w i p)
        * scalarModelMap Y (star (z i) * z j) p q * w j q
        = if p = q then
            (starRingEnd ℂ) (w i p) * (star (z i) * z j) * w j q else 0 := by
      intro q
      by_cases hpq : p = q <;> simp [hpq]
    rw [Finset.sum_congr rfl fun q _ ↦ hterm q,
      Finset.sum_ite_eq Finset.univ p
        (fun q ↦ (starRingEnd ℂ) (w i p) * (star (z i) * z j) * w j q)]
    simp only [Finset.mem_univ, if_true, map_mul, starRingEnd_apply]
    ring
  have hsum : (∑ i : Fin m, ∑ j : Fin m, ∑ p : Y, ∑ q : Y,
      (starRingEnd ℂ) (w i p)
        * scalarModelMap Y (star (z i) * z j) p q * w j q)
      = ∑ p : Y, (starRingEnd ℂ) (∑ i : Fin m, z i * w i p)
          * (∑ j : Fin m, z j * w j p) := by
    have h1 : ∀ i j : Fin m, (∑ p : Y, ∑ q : Y,
        (starRingEnd ℂ) (w i p)
          * scalarModelMap Y (star (z i) * z j) p q * w j q)
        = ∑ p : Y, (starRingEnd ℂ) (z i * w i p) * (z j * w j p) :=
      fun i j ↦ Finset.sum_congr rfl fun p _ ↦ hcollapse i j p
    simp_rw [h1]
    rw [sum_comm₃ (fun (i j : Fin m) (p : Y) ↦
      (starRingEnd ℂ) (z i * w i p) * (z j * w j p))]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [map_sum]
    exact (Finset.sum_mul_sum Finset.univ Finset.univ
      (fun i ↦ (starRingEnd ℂ) (z i * w i p)) (fun j ↦ z j * w j p)).symm
  have hreal : (∑ p : Y, (starRingEnd ℂ) (∑ i : Fin m, z i * w i p)
        * (∑ j : Fin m, z j * w j p))
      = (((∑ p : Y, Complex.normSq (∑ i : Fin m, z i * w i p)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [mul_comm, Complex.mul_conj]
  rw [hsum, hreal]
  refine ⟨by simp, ?_⟩
  simp only [Complex.ofReal_re]
  exact Finset.sum_nonneg fun p _ ↦ Complex.normSq_nonneg _

/-- **The identity trace on `ℂ` is quasidiagonal**, with every defect
identically zero: the models are the scalar matrices in `M_2(ℂ)`, the maps are
exactly multiplicative and unital, and the normalized trace of `z · 1` is `z`
on the nose.

`ℂ` is separable, nuclear (`CStarExactness.isNuclearCStarAlgebra_complex`) and
satisfies the UCT, and the identity is a faithful tracial state on it, so this
is the Tikuisis--White--Winter theorem at its smallest instance --- proved,
not assumed.  It also shows `IsQuasidiagonalTrace` is satisfiable at an
algebra that is not the zero ring, so the negative results of
`Sofic.TikuisisWhiteWinterSites` are not vacuous. -/
theorem isQuasidiagonalTrace_complex : IsQuasidiagonalTrace (fun z : ℂ ↦ z) := by
  refine ⟨{ space := fun _ ↦ ShulmanTrace.twoDimModel
            map := fun _ ↦ scalarModelMap ShulmanTrace.twoDimModel
            map_one := fun _ ↦ scalarModelMap_one _
            completelyPositive := fun _ ↦
              isCompletelyPositiveOnMatrices_scalarModelMap _
            tendsto_mul := fun z w ↦ ?_
            tendsto_trace := fun z ↦ ?_ }⟩
  · exact ShulmanTrace.tendsto_zero_of_eq_zero fun _ ↦ by
      rw [scalarModelMap_mul, sub_self, norm_zero]
  · exact ShulmanTrace.tendsto_zero_of_eq_zero fun _ ↦ by
      rw [normTrace_scalarModelMap _ ShulmanTrace.card_twoDimModel_pos,
        sub_self, norm_zero]

/-- **Every character is a quasidiagonal trace** --- at *any* unital
C⋆-algebra, including infinite-dimensional ones.

A unital `⋆`-homomorphism `π : A → ℂ` pulls the identity trace on `ℂ` back
along itself, and `QuasidiagonalTraceModel.comp` transports the models: the
composite `φₙ ∘ π` is again unital, completely positive and exactly as
multiplicative, because `π` is exactly multiplicative.  So the models are the
scalar matrices `π(a) · 1`.

This is a second unconditional instance of the conclusion of
Tikuisis--White--Winter, and unlike `isQuasidiagonalTrace_complex` it is not
confined to a finite-dimensional algebra: every commutative unital
C⋆-algebra `C(X)` has one for each point of `X`, by evaluation.  It is of
course not a special case of the *theorem* in any useful sense --- a character
is quasidiagonal for reasons that have nothing to do with nuclearity or the
UCT --- but it does show the conclusion is reachable here at algebras where
`IsQuasidiagonalTrace` is not about matrices. -/
theorem isQuasidiagonalTrace_of_character (π : A →⋆ₐ[ℂ] ℂ) :
    IsQuasidiagonalTrace (fun a : A ↦ π a) :=
  isQuasidiagonalTrace_complex.comp π

end

end Quasidiagonal
end GroupApproximation
