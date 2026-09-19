import GroupApproximation.Analysis.ShulmanTraceClasses
import GroupApproximation.Analysis.PreliminaryInequalitiesPrinted
import GroupApproximation.Analysis.MaximalGroupCStarTrace

/-!
# Hyperlinear and MF traces are one definition with two norms

Shulman's two trace classes are the same five clauses; the only difference is
which norm measures the three *defect* clauses.  Read from the Preliminaries
("Traces") of arXiv:2507.22783v3 — the same list also opens the Preliminaries
of arXiv:2508.00125 — the hyperlinear trace asks for maps `φₙ : A → M_{kₙ}`
with, for all `a, b ∈ A` and `λ, μ ∈ ℂ`,

```text
lim ‖φₙ(ab) − φₙ(a)φₙ(b)‖₂ = 0
lim ‖φₙ(λa + μb) − λφₙ(a) − μφₙ(b)‖₂ = 0
lim ‖φₙ(a⋆) − φₙ(a)⋆‖₂ = 0
supₙ ‖φₙ(a)‖ < ∞
lim |τ(a) − tr φₙ(a)| = 0
```

and the MF trace asks for the identical list with every `‖·‖₂` replaced by the
operator norm `‖·‖`.

Two clauses are *not* parameterized, and getting that wrong would make the
comparison below false rather than merely ugly.  The boundedness clause is in
the **operator** norm in both definitions, and the trace clause is the ordinary
modulus on `ℂ` in both.  So `TraceApproximationModel` takes the defect norm as
a parameter and holds those two fixed.

`ShulmanTraceClasses.MFTraceModel` is the operator-norm member of this family
— `isMFTrace_iff_isTracialState_and_nonempty_opNorm` says so in both directions,
by an identity
transfer of all five fields — and `IsHyperlinearTrace` is the
Hilbert–Schmidt member.  Then

```text
every MF trace is hyperlinear
```

is `isHyperlinearTrace_of_isMFTrace`, and it is one squeeze against the first
printed inequality `‖x‖₂ ≤ ‖x‖` (`PrelimNotation.hsNorm_le_l2_opNorm`), with
the two unparameterized clauses carried across unchanged.  That is the cheap
sanity check that the two definitions are parameterized correctly: if the sup
clause had been parameterized too, this proof would not close, because
`‖·‖₂ ≤ ‖·‖` runs the wrong way for a *lower* bound on a supremum.

## What is deliberately not here

The classical pair with completely positive maps — an amenable trace is the
`‖·‖₂` version with `φₙ` required ccp, a quasidiagonal trace the `‖·‖`
version — would need a complete-positivity predicate for maps into matrix
algebras, which this repository does not have.  Defining it wrongly would be
worse than leaving the lattice incomplete, so only the two ccp-free classes
are here.

## The ∗-linearity licence, recorded and not used

Shulman remarks that in the definition of an MF trace one may additionally
require the maps `φₙ` to be `⋆`-linear, citing Rainone–Schafhauser,
*Crossed products of nuclear C⋆-algebras and their traces*, Adv. Math. 347
(2019) 105–149, Prop. 2.2, and notes the same argument works for hyperlinear
traces.  The licence is recorded here because it is the step that would make
Schafhauser's exactly-linear Definition 2.1 importable.  This development does
not use it: `Sofic.ShulmanMFTraceBridge` closes against the asymptotic
definition as written, which is the stronger position, so the strengthening is
never needed and is not assumed anywhere.
-/

open Filter Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace GroupApproximation
namespace ShulmanTrace

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]

/-! ## One family, parameterized by the defect norm -/

/-- Matrix models for a trace, with the three defect clauses measured in a
norm `d` supplied as a parameter.

The last two clauses are *not* parameterized by `d`: `bounded` is the operator
norm and `tendsto_trace` the modulus on `ℂ`, in both definitions.

The limits are taken along a filter `l` rather than fixed at `atTop`.  Both
trace classes read `atTop`, and that is how `IsHyperlinearTrace` instantiates
it; the parameter is here because a construction can land along a finer filter
than the one it is wanted along, and because it costs nothing. -/
structure TraceApproximationModel (l : Filter ℕ)
    (d : ∀ Y : FiniteModel, Matrix Y Y ℂ → ℝ) (τ : A → ℂ) where
  /-- The finite matrix sizes. -/
  space : ℕ → FiniteModel
  /-- The maps `φₙ : A → M_{kₙ}`, not assumed linear. -/
  map : ∀ n : ℕ, A → Matrix (space n) (space n) ℂ
  /-- Asymptotic multiplicativity, in the defect norm `d`. -/
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ d (space n) (map n (a * b) - map n a * map n b))
      l (nhds 0)
  /-- Asymptotic linearity, in the defect norm `d`. -/
  tendsto_linear : ∀ (c₁ c₂ : ℂ) (a b : A),
    Tendsto (fun n ↦ d (space n)
        (map n (c₁ • a + c₂ • b) - c₁ • map n a - c₂ • map n b)) l (nhds 0)
  /-- Asymptotic `⋆`-compatibility, in the defect norm `d`. -/
  tendsto_star : ∀ a : A,
    Tendsto (fun n ↦ d (space n) (map n (star a) - (map n a)ᴴ))
      l (nhds 0)
  /-- Pointwise boundedness, in the operator norm whatever `d` and `l` are. -/
  bounded : ∀ a : A, ∃ C : ℝ, ∀ n : ℕ, ‖map n a‖ ≤ C
  /-- The normalized traces converge to `τ`, whatever `d` is. -/
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ a - normTrace (space n) (map n a)‖) l (nhds 0)

/-! ## The operator-norm member is the MF trace already defined -/

/-- An MF-trace model, read as a member of the parameterized family. -/
def MFTraceModel.toApproximationModel {τ : A → ℂ} (M : MFTraceModel τ) :
    TraceApproximationModel atTop (fun _ B ↦ ‖B‖) τ where
  space := M.space
  map := M.map
  tendsto_mul := M.tendsto_mul
  tendsto_linear := M.tendsto_linear
  tendsto_star := M.tendsto_star
  bounded := M.bounded
  tendsto_trace := M.tendsto_trace

/-- The operator-norm member of the family, read back as an MF-trace model. -/
def TraceApproximationModel.toMFTraceModel {τ : A → ℂ}
    (M : TraceApproximationModel atTop (fun _ B ↦ ‖B‖) τ) : MFTraceModel τ where
  space := M.space
  map := M.map
  tendsto_mul := M.tendsto_mul
  tendsto_linear := M.tendsto_linear
  tendsto_star := M.tendsto_star
  bounded := M.bounded
  tendsto_trace := M.tendsto_trace

/-! ## The Hilbert–Schmidt member is the hyperlinear trace -/

/-- **Shulman's hyperlinear trace**: an actual tracial state satisfying the
five approximation clauses, with the three defect clauses measured in the
normalized Hilbert–Schmidt norm.  The boundedness and trace clauses are the
same as for an MF trace. -/
def IsHyperlinearTrace (τ : A → ℂ) : Prop :=
  IsTracialState τ ∧
    Nonempty (TraceApproximationModel atTop (fun Y B ↦ hsNorm Y B) τ)

/-- The defect comparison, in the shape the five clauses consume it: an
operator-norm null sequence of matrices is Hilbert–Schmidt null, by the first
printed inequality `‖x‖₂ ≤ ‖x‖` and a squeeze. -/
theorem tendsto_hsNorm_of_tendsto_opNorm {l : Filter ℕ} {Y : ℕ → FiniteModel}
    {X : ∀ n : ℕ, Matrix (Y n) (Y n) ℂ}
    (h : Tendsto (fun n ↦ ‖X n‖) l (nhds 0)) :
    Tendsto (fun n ↦ hsNorm (Y n) (X n)) l (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ hsNorm_nonneg (Y n) (X n))
  · exact Eventually.of_forall fun n ↦
      PrelimNotation.hsNorm_le_l2_opNorm (Y n) (X n)
  · exact h

/-- **The comparison.**  An operator-norm model is a Hilbert–Schmidt model:
the three defect clauses weaken through `‖x‖₂ ≤ ‖x‖`, and the two
unparameterized clauses are carried across unchanged. -/
def TraceApproximationModel.toHilbertSchmidt {l : Filter ℕ} {τ : A → ℂ}
    (M : TraceApproximationModel l (fun _ B ↦ ‖B‖) τ) :
    TraceApproximationModel l (fun Y B ↦ hsNorm Y B) τ where
  space := M.space
  map := M.map
  tendsto_mul a b :=
    tendsto_hsNorm_of_tendsto_opNorm (Y := M.space)
      (X := fun n ↦ M.map n (a * b) - M.map n a * M.map n b)
      (M.tendsto_mul a b)
  tendsto_linear c₁ c₂ a b :=
    tendsto_hsNorm_of_tendsto_opNorm (Y := M.space)
      (X := fun n ↦ M.map n (c₁ • a + c₂ • b) - c₁ • M.map n a - c₂ • M.map n b)
      (M.tendsto_linear c₁ c₂ a b)
  tendsto_star a :=
    tendsto_hsNorm_of_tendsto_opNorm (Y := M.space)
      (X := fun n ↦ M.map n (star a) - (M.map n a)ᴴ)
      (M.tendsto_star a)
  bounded := M.bounded
  tendsto_trace := M.tendsto_trace

/-! ## The two statements the parameterization buys -/

/-- `IsMFTrace` is tracial-state data together with the operator-norm member
of the parameterized family — both directions, by an identity transfer of all
five approximation clauses. -/
theorem isMFTrace_iff_isTracialState_and_nonempty_opNorm (τ : A → ℂ) :
    IsMFTrace τ ↔ IsTracialState τ ∧
      Nonempty (TraceApproximationModel atTop (fun _ B ↦ ‖B‖) τ) := by
  constructor
  · rintro ⟨hτ, ⟨M⟩⟩
    exact ⟨hτ, ⟨M.toApproximationModel⟩⟩
  · rintro ⟨hτ, ⟨M⟩⟩
    exact ⟨hτ, ⟨M.toMFTraceModel⟩⟩

/-- **Every MF trace is hyperlinear.**  The two definitions differ only in the
norm on the three defect clauses, and `‖x‖₂ ≤ ‖x‖`. -/
theorem isHyperlinearTrace_of_isMFTrace {τ : A → ℂ} (h : IsMFTrace τ) :
    IsHyperlinearTrace τ := by
  obtain ⟨hτ, ⟨M⟩⟩ := h
  exact ⟨hτ, ⟨M.toApproximationModel.toHilbertSchmidt⟩⟩

/-! ## The canonical trace of the full group C⋆-algebra, bundled -/

/-- The canonical trace of `C⋆(G)`, bundled as a tracial state: unital,
positive on `x⋆x`, and invariant under swapping the factors of a product.
Faithfulness is absent and is not expected — that is why `TracialState` exists
alongside `FaithfulTracialState`. -/
def canonicalMaximalTracialState (G : Type*) [Group G] :
    TracialState (MaximalGroupCStar G) where
  toLinearMap := (canonicalMaximalTrace G).toLinearMap
  map_one := canonicalMaximalTrace_one G
  map_star_mul_self_nonneg := canonicalMaximalTrace_star_mul_self_nonneg G
  map_mul_comm := canonicalMaximalTrace_mul_comm G

@[simp]
theorem canonicalMaximalTracialState_apply (G : Type*) [Group G]
    (a : MaximalGroupCStar G) :
    canonicalMaximalTracialState G a = canonicalMaximalTrace G a :=
  rfl

end

end ShulmanTrace
end GroupApproximation
