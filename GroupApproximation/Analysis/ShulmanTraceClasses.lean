import GroupApproximation.Analysis.FaithfulTracialState
import GroupApproximation.Sofic.HyperlinearAmplification

/-!
# Shulman's trace classes: tracial states and MF traces

Two definitional layers, both frozen here so that downstream results quote
them rather than re-invent them.

* `TracialState` is the repository's `FaithfulTracialState` with faithfulness
  deleted.  The canonical trace of a full group C⋆-algebra need not be
  faithful, and none of the MF-trace theory uses faithfulness, so the weaker
  notion is the right hypothesis surface.

* `MFTraceModel` / `IsMFTrace` is Shulman's MF-trace condition, transcribed
  from *Sections and cones*, arXiv:2507.22783v3: a trace `τ` on `A` is an MF
  trace when there are maps `φₙ : A → M_{kₙ}` with, as `n → ∞`,

  ```text
  ‖φₙ(ab) − φₙ(a)φₙ(b)‖ → 0,
  ‖φₙ(λa + μb) − λ φₙ(a) − μ φₙ(b)‖ → 0,
  ‖φₙ(a⋆) − φₙ(a)⋆‖ → 0,
  supₙ ‖φₙ(a)‖ < ∞,
  |τ(a) − tr φₙ(a)| → 0,
  ```

  every norm the operator norm and `tr` the normalized trace.

**The weakness of the hypothesis is load-bearing and must not be repaired.**
The maps `φₙ` are required to be neither positive, nor unital, nor completely
positive, nor exactly linear, nor exactly `⋆`-preserving — only
*asymptotically* linear and *asymptotically* `⋆`-preserving, with a pointwise
norm bound.  Every downstream theorem that concludes something *from* an MF
trace gets its strength from exactly this.  For contrast, Schafhauser,
arXiv:2306.02498, Definition 2.1 asks for genuinely linear, genuinely
self-adjoint maps; that is a strictly stronger hypothesis and is why his
Proposition 2.2 is not directly importable against this definition.

Nothing here requires `A` to be a C⋆-algebra: the five conditions only
measure norms on the matrix side, so the ambient is the same complex
`⋆`-algebra signature that `FaithfulTracialState` uses.  The intended
instances are unital C⋆-algebras, which carry that signature.
-/

open Filter Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace GroupApproximation

noncomputable section

/-- A tracial state on a unital complex `⋆`-algebra: a unital linear
functional, nonnegative on elements `x⋆ x`, and invariant under swapping the
factors of a product.

This is `FaithfulTracialState` with the faithfulness clause removed. -/
structure TracialState (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] where
  toLinearMap : A →ₗ[ℂ] ℂ
  map_one : toLinearMap 1 = 1
  map_star_mul_self_nonneg : ∀ x : A, 0 ≤ toLinearMap (star x * x)
  map_mul_comm : ∀ x y : A, toLinearMap (x * y) = toLinearMap (y * x)

namespace TracialState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

instance : CoeFun (TracialState A) fun _ ↦ A → ℂ :=
  ⟨fun τ ↦ τ.toLinearMap⟩

@[simp]
theorem map_zero (τ : TracialState A) : τ 0 = 0 :=
  τ.toLinearMap.map_zero

@[simp]
theorem map_add (τ : TracialState A) (x y : A) : τ (x + y) = τ x + τ y :=
  τ.toLinearMap.map_add x y

@[simp]
theorem map_sub (τ : TracialState A) (x y : A) : τ (x - y) = τ x - τ y :=
  τ.toLinearMap.map_sub x y

@[simp]
theorem map_smul (τ : TracialState A) (c : ℂ) (x : A) : τ (c • x) = c • τ x :=
  τ.toLinearMap.map_smul c x

@[simp]
theorem apply_one (τ : TracialState A) : τ 1 = 1 :=
  τ.map_one

end TracialState

namespace FaithfulTracialState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- Forget faithfulness. -/
def toTracialState (τ : FaithfulTracialState A) : TracialState A where
  toLinearMap := τ.toLinearMap
  map_one := τ.map_one
  map_star_mul_self_nonneg := τ.map_star_mul_self_nonneg
  map_mul_comm := τ.map_mul_comm

@[simp]
theorem coe_toTracialState (τ : FaithfulTracialState A) (x : A) :
    τ.toTracialState x = τ x :=
  rfl

end FaithfulTracialState

/-! ## Shulman's MF trace -/

namespace ShulmanTrace

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- The matrix models witnessing that `τ` is an MF trace, exactly as in
Shulman, arXiv:2507.22783v3.

Read the fields as `‖φₙ(ab) − φₙ(a)φₙ(b)‖ → 0`, `‖φₙ(λa + μb) − λ φₙ(a) −
μ φₙ(b)‖ → 0`, `‖φₙ(a⋆) − φₙ(a)⋆‖ → 0`, `supₙ ‖φₙ(a)‖ < ∞` and
`|τ(a) − tr φₙ(a)| → 0`, all norms being the operator norm and `tr` the
normalized trace `normTrace`.

The maps carry no positivity, unitality, complete positivity, exact linearity
or exact `⋆`-compatibility; strengthening any clause would weaken every
theorem that takes an MF trace as input. -/
structure MFTraceModel (τ : A → ℂ) where
  /-- The finite matrix sizes. -/
  space : ℕ → FiniteModel
  /-- The maps `φₙ : A → M_{kₙ}`, not assumed linear. -/
  map : ∀ n : ℕ, A → Matrix (space n) (space n) ℂ
  /-- Asymptotic multiplicativity in operator norm. -/
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) atTop (nhds 0)
  /-- Asymptotic linearity in operator norm. -/
  tendsto_linear : ∀ (l m : ℂ) (a b : A),
    Tendsto (fun n ↦ ‖map n (l • a + m • b) - l • map n a - m • map n b‖)
      atTop (nhds 0)
  /-- Asymptotic `⋆`-compatibility in operator norm. -/
  tendsto_star : ∀ a : A,
    Tendsto (fun n ↦ ‖map n (star a) - (map n a)ᴴ‖) atTop (nhds 0)
  /-- Pointwise boundedness, uniform in `n`. -/
  bounded : ∀ a : A, ∃ C : ℝ, ∀ n : ℕ, ‖map n a‖ ≤ C
  /-- The normalized traces of the models converge to `τ`. -/
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ a - normTrace (space n) (map n a)‖) atTop (nhds 0)

/-- `τ` is an MF trace: matrix models in the sense of `MFTraceModel` exist. -/
def IsMFTrace (τ : A → ℂ) : Prop :=
  Nonempty (MFTraceModel τ)

theorem isMFTrace_iff (τ : A → ℂ) :
    IsMFTrace τ ↔ Nonempty (MFTraceModel τ) :=
  Iff.rfl

/-- A real sequence tending to zero eventually sits below any positive bound.
This is the only shape in which the five limit clauses are consumed: a finite
test set contributes finitely many eventual conditions, and one late index
satisfies all of them. -/
theorem eventually_le_of_tendsto_zero {f : ℕ → ℝ}
    (h : Tendsto f atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, f n ≤ ε :=
  (h.eventually_lt_const hε).mono fun _ hn ↦ hn.le

end ShulmanTrace

end

end GroupApproximation
