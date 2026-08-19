import GroupApproximation.Analysis.ShulmanTracePositiveControls

/-!
# Quasidiagonal traces: the conclusion of Tikuisis--White--Winter

`INT.11` prints *"all amenable groups are MF, by quasidiagonality"* and
`CY.12c` prints the same implication at one group.  Both cite the
Tikuisis--White--Winter theorem, *Quasidiagonality of nuclear C⋆-algebras*,
Ann. of Math. (2) **185** (2017), 229--284.  Until now the repository typed
that citation only at its far end, as
`QuasidiagonalMF.AmenableMFInput` --- the bare group implication
`amenable ⟹ operator-MF`.  That is not the theorem; it is several reductions
downstream of it, and stating the input there hides which of those reductions
are theorems and which are further citations.

This file supplies the near end: **the notion in which TWW's conclusion is
stated.**  `Analysis.TikuisisWhiteWinter` then states the theorem itself, and
proves that every step between it and the printed group implication is either
machine-checked here or a separately named input.

## The definition

A trace `τ` on a unital C⋆-algebra `A` is **quasidiagonal** when there are
unital completely positive maps `φₙ : A → M_{kₙ}` with

```text
‖φₙ(ab) − φₙ(a)φₙ(b)‖ → 0,      tr φₙ(a) → τ(a),
```

the first norm the operator norm and `tr` the normalized trace.  That is
`QuasidiagonalTraceModel` below, field for field.  Complete positivity is
spelled in the *form* sense --- the scalar matrix `[φ(aᵢ⋆aⱼ)]` is positive
semidefinite for every finite tuple --- which is the shape
`Analysis.LanceMatrixArveson` already uses for maps into a matrix algebra and
which needs no C⋆-instance on the matrix side beyond the scoped operator
norm.

## Its relation to Shulman's MF trace

`ShulmanTrace.MFTraceModel` asks for strictly less in every clause: its maps
are not required to be positive, unital, completely positive, exactly linear
or exactly `⋆`-preserving.  So a quasidiagonal trace *should* be an MF trace,
and `QuasidiagonalTraceModel.toMFTraceModel` proves it --- except for one
thing.  Two clauses of `MFTraceModel` are asymptotic versions of properties a
ucp map has *automatically*:

* `φₙ(a⋆) = φₙ(a)⋆`, because a positive map is `⋆`-preserving;
* `‖φₙ(a)‖ ≤ ‖a‖`, because a unital completely positive map is a contraction
  (Stinespring's dilation theorem: `φ = V⋆ π(·) V` with `V` an isometry).

Neither is proved in this repository, so neither is silently assumed.  They
are carried by `UCPSelfAdjointContractive`, a **separate** typed input, and
every theorem that consumes them says so in its type.  Keeping them out of
`QuasidiagonalTraceModel` is deliberate: it means the structure is a literal
transcription of TWW's conclusion and nothing more, so a reader checking the
transcription against the paper has nothing extra to check.

**`UCPSelfAdjointContractive` is dischargeable in principle and TWW is not --
but NOT against the predicate below, and the earlier claim that it was is
withdrawn (2026-08-19).**  The repository carries the Stinespring dilation for
completely positive maps into `B(H)`
(`Analysis.CStarStinespringDilation.stinespring_dilation`, with its ten-module
chain), and the missing steps were recorded here as (i) transporting the
form-sense complete positivity below into `CStarExactness.IsCompletelyPositive`
and (ii) identifying `Matrix Y Y ℂ` with `B(ℂᵏ)`.  Step (ii) is bookkeeping.
**Step (i) is false**, because `IsCompletelyPositiveOnMatrices` constrains only
the *real part* of the form, and a matrix whose Hermitian part is positive
semidefinite need not be positive semidefinite -- its anti-Hermitian part is
invisible to the predicate.

The counterexample is two-by-two.  Let `N = !![0, 1; -1, 0]`, so `Nᴴ = -N` and
`⟪W, N W⟫` is purely imaginary for every `W`.  Take `A = ℂ × ℂ`, `Y = Fin 2`,
and

```text
    φ (z, w)  =  z • (½ • 1 + N)  +  w • (½ • 1 - N).
```

`φ` is `ℂ`-linear, `φ 1 = 1`, and it satisfies
`IsCompletelyPositiveOnMatrices`: for a tuple `aᵢ = (zᵢ, wᵢ)` the double sum
collapses to `Re ⟪U, (½ + N) U⟫ + Re ⟪V, (½ − N) V⟫` with `U = ∑ zᵢ Wᵢ` and
`V = ∑ wᵢ Wᵢ`, and each term is `½‖·‖²` because `N` contributes nothing to a
real part.  Yet **both** clauses of `UCPSelfAdjointContractive` fail for it:
`φ (star (z, w)) = conj z • (½ + N) + conj w • (½ − N)` while
`(φ (z, w))ᴴ = conj z • (½ − N) + conj w • (½ + N)`, unequal for `z ≠ w`; and
`‖φ (1, 0)‖ = ‖½ + N‖ = √5 / 2 > 1 = ‖(1, 0)‖`.

**What would actually discharge it** is to strengthen the predicate to genuine
positivity -- add the clause that the form's imaginary part vanishes, which is
what complete positivity means and what Tikuisis--White--Winter supplies, so
the input does not get stronger than the theorem.  With that clause the
`⋆`-preservation half is short and needs no dilation: apply the two-element
tuple `a = (μ • 1, b)` at vectors `u, v`, whose form is
`|μ|²‖u‖² + conj μ • ⟪u, φ b v⟫ + μ • ⟪v, φ (star b) u⟫ + ⟪v, φ (star b * b) v⟫`;
reality at `μ = 0, 1, i` gives `Re ⟪v, φ (star b) u⟫ = Re ⟪u, φ b v⟫` and
`Im ⟪v, φ (star b) u⟫ = −Im ⟪u, φ b v⟫`, which is `φ (star b) = (φ b)ᴴ`.  The
contractivity half still wants Stinespring, or the Kadison--Schwarz inequality
for two-positive maps.  Nothing of the kind is available for TWW.

**No inhabitant of `UCPSelfAdjointContractive` is constructed here, and none of
`QuasidiagonalTraceModel` at any nontrivial algebra.**
-/

namespace GroupApproximation
namespace Quasidiagonal

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-! ## Complete positivity, in the form sense -/

/-- **Complete positivity for a map into a matrix algebra**, stated on
quadratic forms: for every finite tuple `a : Fin m → A` and every tuple of
vectors `w`, the scalar

`∑ᵢⱼ ⟪wᵢ, φ(aᵢ⋆ aⱼ) wⱼ⟫`

is nonnegative.  This says exactly that the `m × m` block matrix
`[φ(aᵢ⋆ aⱼ)]` over `M_Y` is positive semidefinite, which is the textbook
definition of complete positivity.

The form shape is the one `Analysis.LanceMatrixArveson` uses for the same kind
of map (its `hform` hypothesis), and it is preferred here over
`CStarExactness.IsCompletelyPositive` for a concrete reason: that predicate is
stated for `CStarMatrix` over C⋆-algebras, and `Matrix Y Y ℂ` carries its
C⋆-structure only through a locally assembled instance
(`Analysis.PolarLiftingMatrixBlocks`), deliberately not registered globally.
Nothing below needs complete positivity at all --- it is here because TWW's
statement has it, not because a proof consumes it. -/
def IsCompletelyPositiveOnMatrices (Y : FiniteModel) (φ : A → Matrix Y Y ℂ) :
    Prop :=
  ∀ (m : ℕ) (a : Fin m → A) (w : Fin m → Y → ℂ),
    0 ≤ (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
      (starRingEnd ℂ) (w i x) * φ (star (a i) * a j) x y * w j y).re

/-- The zero map is completely positive: every form vanishes.  A smoke test on
the orientation of the inequality, nothing more. -/
theorem isCompletelyPositiveOnMatrices_zero (Y : FiniteModel) :
    IsCompletelyPositiveOnMatrices Y (fun _ : A ↦ (0 : Matrix Y Y ℂ)) := by
  intro m a w
  simp

/-- **Complete positivity specializes to ordinary positivity.**  Taking a
one-element tuple, the defining condition says that each single matrix
`φ (a⋆ a)` has nonnegative quadratic form --- that is, `φ` carries the
positive elements `a⋆ a` of `A` to positive matrices.

Complete positivity is the same statement for tuples, uniformly in the tuple
length, and this is the `m = 1` instance.  It is recorded because it is the
clause a reader checks first when confirming that
`IsCompletelyPositiveOnMatrices` is the intended predicate rather than an
unrelated inequality. -/
theorem IsCompletelyPositiveOnMatrices.form_nonneg {Y : FiniteModel}
    {φ : A → Matrix Y Y ℂ} (h : IsCompletelyPositiveOnMatrices Y φ) (a : A)
    (w : Y → ℂ) :
    0 ≤ (∑ x : Y, ∑ y : Y,
      (starRingEnd ℂ) (w x) * φ (star a * a) x y * w y).re := by
  simpa using h 1 (fun _ ↦ a) (fun _ ↦ w)

/-! ## The conclusion of Tikuisis--White--Winter -/

/-- **A quasidiagonal trace**, in the sense of Tikuisis--White--Winter: unital
completely positive matrix models that are asymptotically multiplicative in
operator norm and whose normalized traces converge to `τ`.

Read the fields as

```text
φₙ : A → M_{kₙ} linear,   φₙ(1) = 1,   φₙ completely positive,
‖φₙ(ab) − φₙ(a)φₙ(b)‖ → 0,            |τ(a) − tr φₙ(a)| → 0.
```

Nothing here asks for positive matrix dimensions.  `MFTraceModel` does not
either, and `ShulmanTrace.MFTraceModel.exists_shift` shows why it need not:
the trace clause at the unit already forces all but finitely many models to be
nonempty.  Keeping the clause out leaves the input as weak as the theorem
that supplies it. -/
structure QuasidiagonalTraceModel (τ : A → ℂ) where
  /-- The finite matrix sizes `kₙ`. -/
  space : ℕ → FiniteModel
  /-- The maps `φₙ : A → M_{kₙ}`, genuinely `ℂ`-linear. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  /-- Each `φₙ` is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each `φₙ` is completely positive. -/
  completelyPositive : ∀ n : ℕ,
    IsCompletelyPositiveOnMatrices (space n) ⇑(map n)
  /-- Asymptotic multiplicativity in operator norm. -/
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) atTop (nhds 0)
  /-- The normalized traces of the models converge to `τ`. -/
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ a - normTrace (space n) (map n a)‖) atTop (nhds 0)

/-- `τ` is a quasidiagonal trace: models in the sense of
`QuasidiagonalTraceModel` exist.  This is the conclusion of the
Tikuisis--White--Winter theorem, and the property that theorem is the only
known source of outside the classes already machine-checked in
`Analysis.AmenableMFInput`. -/
def IsQuasidiagonalTrace (τ : A → ℂ) : Prop :=
  Nonempty (QuasidiagonalTraceModel τ)

theorem isQuasidiagonalTrace_iff (τ : A → ℂ) :
    IsQuasidiagonalTrace τ ↔ Nonempty (QuasidiagonalTraceModel τ) :=
  Iff.rfl

/-! ## The two automatic properties of a ucp map, as one typed input -/

/-- **The standard facts about unital completely positive maps into matrices**
that the reduction below consumes: such a map is `⋆`-preserving and
contractive.

Both are theorems, not hypotheses, in the operator-algebra literature: a
positive map preserves adjoints, and a unital completely positive map is the
compression `V⋆ π(·) V` of a `⋆`-representation along an isometry
(Stinespring, *Positive functions on C⋆-algebras*, Proc. Amer. Math. Soc. 6
(1955), 211--216; see also Brown--Ozawa, *C⋆-algebras and Finite-Dimensional
Approximations*, Chapter 1), hence a contraction.  This development proves
neither, so they are named, typed, and passed explicitly wherever used.

**Why they are not fields of `QuasidiagonalTraceModel`.**  That structure is
the literal conclusion of Tikuisis--White--Winter.  Adding clauses to it would
make the theorem this repository *assumes* stronger than the theorem the
literature *proves*, which is the wrong direction for an input; and it would
make the transcription harder to check against the paper.  Kept separate, the
two facts appear in the type of every theorem that uses them and are visible
to `scripts/check_non_mf_unconditional.py --audit-corpus` under their own
name.

**This input is NOT dischargeable against `IsCompletelyPositiveOnMatrices` as
that predicate currently stands**; the module docstring carries the two-by-two
counterexample and the clause that has to be added first.  No inhabitant is
constructed here, and none can be until the predicate is corrected.

It is a structure rather than a bare implication for the same reason
`QuasidiagonalMF.AmenableMFInput` is: consuming it then leaves a visible
binder in the type of every theorem that does, and the name is picked up by
`scripts/check_non_mf_unconditional.py --audit-corpus` as an assumed and
uninhabited one. -/
structure UCPSelfAdjointContractive : Prop where
  /-- A unital completely positive map into a matrix algebra preserves
  adjoints. -/
  map_star : ∀ (B : Type u) (_ : CStarAlgebra B) (Y : FiniteModel)
    (φ : B →ₗ[ℂ] Matrix Y Y ℂ), φ 1 = 1 →
      IsCompletelyPositiveOnMatrices Y ⇑φ → ∀ b : B, φ (star b) = (φ b)ᴴ
  /-- A unital completely positive map into a matrix algebra is a
  contraction. -/
  norm_le : ∀ (B : Type u) (_ : CStarAlgebra B) (Y : FiniteModel)
    (φ : B →ₗ[ℂ] Matrix Y Y ℂ), φ 1 = 1 →
      IsCompletelyPositiveOnMatrices Y ⇑φ → ∀ b : B, ‖φ b‖ ≤ ‖b‖

/-! ## Quasidiagonal traces are MF traces -/

/-- **A quasidiagonal trace is an MF trace.**  Every clause of
`ShulmanTrace.MFTraceModel` is weaker than the corresponding clause here:
exact linearity gives asymptotic linearity with defect identically `0`, exact
`⋆`-preservation gives the asymptotic form the same way, and contractivity
gives the pointwise bound with the constant `‖a‖`.  The multiplicative and
trace clauses are transcribed unchanged.

The `⋆` and boundedness clauses are the two automatic properties of a ucp map,
and they enter through the explicit input `hucp` rather than being assumed:
this theorem's type records that the passage from TWW's conclusion to
Shulman's hypothesis is not free in a development that has not formalized
Stinespring's dilation for matrix targets. -/
def QuasidiagonalTraceModel.toMFTraceModel {τ : A → ℂ}
    (hucp : UCPSelfAdjointContractive.{u}) (M : QuasidiagonalTraceModel τ) :
    ShulmanTrace.MFTraceModel τ where
  space := M.space
  map n := ⇑(M.map n)
  tendsto_mul := M.tendsto_mul
  tendsto_linear l m a b := ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
    simp only [map_add, map_smul, add_sub_cancel_left, sub_self, norm_zero]
  tendsto_star a := ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
    simp only [hucp.map_star A inferInstance (M.space n) (M.map n)
      (M.map_one n) (M.completelyPositive n) a, sub_self, norm_zero]
  bounded a := ⟨‖a‖, fun n ↦ hucp.norm_le A inferInstance (M.space n)
    (M.map n) (M.map_one n) (M.completelyPositive n) a⟩
  tendsto_trace := M.tendsto_trace

/-- The proposition-level form: a quasidiagonal trace is an MF trace. -/
theorem isMFTrace_of_isQuasidiagonalTrace {τ : A → ℂ}
    (hucp : UCPSelfAdjointContractive.{u}) (h : IsQuasidiagonalTrace τ) :
    ShulmanTrace.IsMFTrace τ := by
  obtain ⟨M⟩ := h
  exact ⟨M.toMFTraceModel hucp⟩

end

end Quasidiagonal
end GroupApproximation
