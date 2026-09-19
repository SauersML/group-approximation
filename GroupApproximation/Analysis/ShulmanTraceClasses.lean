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

/-- Pull a tracial state back along a unital `⋆`-algebra homomorphism. -/
def compStarAlgHom {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (τ : TracialState B) (π : A →⋆ₐ[ℂ] B) : TracialState A where
  toLinearMap := τ.toLinearMap.comp π.toLinearMap
  map_one := by
    change τ.toLinearMap (π.toLinearMap 1) = 1
    have hcoe : π.toLinearMap 1 = π.toRingHom 1 := rfl
    rw [hcoe, π.toRingHom.map_one]
    exact τ.map_one
  map_star_mul_self_nonneg x := by
    change 0 ≤ τ.toLinearMap (π.toLinearMap (star x * x))
    have hcoe : π.toLinearMap (star x * x) = π.toRingHom (star x * x) := rfl
    have hstar : π.toRingHom (star x) = star (π.toRingHom x) := by
      exact map_star π x
    rw [hcoe, π.toRingHom.map_mul, hstar]
    exact τ.map_star_mul_self_nonneg (π.toRingHom x)
  map_mul_comm x y := by
    change τ.toLinearMap (π.toLinearMap (x * y)) =
      τ.toLinearMap (π.toLinearMap (y * x))
    have hxy : π.toLinearMap (x * y) = π.toRingHom (x * y) := rfl
    have hyx : π.toLinearMap (y * x) = π.toRingHom (y * x) := rfl
    rw [hxy, hyx, π.toRingHom.map_mul, π.toRingHom.map_mul]
    exact τ.map_mul_comm (π.toRingHom x) (π.toRingHom y)

@[simp]
theorem compStarAlgHom_apply {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    (τ : TracialState B) (π : A →⋆ₐ[ℂ] B) (x : A) :
    τ.compStarAlgHom π x = τ (π x) :=
  rfl

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

/-! ## Tracial-state predicate and Shulman's MF trace -/

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-- A function is an actual tracial state when it is the underlying function
of a bundled `TracialState`.  The approximation clauses below do not by
themselves include normalization, positivity, or traciality, whereas the word
"trace" in Shulman's definitions presupposes precisely this datum. -/
def IsTracialState (τ : A → ℂ) : Prop :=
  ∃ σ : TracialState A, ∀ a : A, σ a = τ a

namespace IsTracialState

/-- The underlying function of a bundled tracial state is a tracial state. -/
theorem of_bundled (σ : TracialState A) :
    IsTracialState (fun a : A ↦ σ a) :=
  ⟨σ, fun _ ↦ rfl⟩

/-- Tracial-state data is invariant under pointwise equality. -/
theorem congr {τ υ : A → ℂ} (hτ : IsTracialState τ)
    (h : ∀ a : A, τ a = υ a) : IsTracialState υ := by
  obtain ⟨σ, hσ⟩ := hτ
  exact ⟨σ, fun a ↦ (hσ a).trans (h a)⟩

/-- Tracial states pull back along unital `⋆`-algebra homomorphisms. -/
theorem compStarAlgHom {B : Type*} [Ring B] [StarRing B] [Algebra ℂ B]
    {τ : B → ℂ} (hτ : IsTracialState τ) (π : A →⋆ₐ[ℂ] B) :
    IsTracialState (fun a : A ↦ τ (π a)) := by
  obtain ⟨σ, hσ⟩ := hτ
  exact ⟨σ.compStarAlgHom π, fun a ↦ hσ (π a)⟩

end IsTracialState

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

/-- `τ` is an MF trace: it is an actual tracial state and matrix models in the
sense of `MFTraceModel` exist. -/
def IsMFTrace (τ : A → ℂ) : Prop :=
  IsTracialState τ ∧ Nonempty (MFTraceModel τ)

theorem isMFTrace_iff (τ : A → ℂ) :
    IsMFTrace τ ↔ IsTracialState τ ∧ Nonempty (MFTraceModel τ) :=
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
