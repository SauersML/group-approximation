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
are carried by `UCPContractive`, a **separate** typed input, and
every theorem that consumes them says so in its type.  Keeping them out of
`QuasidiagonalTraceModel` is deliberate: it means the structure is a literal
transcription of TWW's conclusion and nothing more, so a reader checking the
transcription against the paper has nothing extra to check.

**`UCPContractive` is dischargeable and TWW is not, but the route
recorded here was aimed at the wrong obstacle (corrected 2026-08-19).**  The
repository carries the Stinespring dilation for completely positive maps into
`B(H)` (`Analysis.CStarStinespringDilation.stinespring_dilation`, with its
ten-module chain), and the missing steps were recorded as (i) transporting the
form-sense complete positivity below into `CStarExactness.IsCompletelyPositive`
and (ii) identifying `Matrix Y Y ℂ` with `B(ℂᵏ)`.  Step (ii) is bookkeeping.
Step (i) was **impossible**, because `IsCompletelyPositiveOnMatrices` then
constrained only the *real part* of the form, and a matrix whose Hermitian part
is positive semidefinite need not be positive semidefinite -- its
anti-Hermitian part was invisible.  The predicate now carries the reality
clause, so the obstacle is gone; the counterexample below is why it is there.

The counterexample is two-by-two.  Let `N = !![0, 1; -1, 0]`, so `Nᴴ = -N` and
`⟪W, N W⟫` is purely imaginary for every `W`.  Take `A = ℂ × ℂ`, `Y = Fin 2`,
and

```text
    φ (z, w)  =  z • (½ • 1 + N)  +  w • (½ • 1 - N).
```

`φ` is `ℂ`-linear, `φ 1 = 1`, and it satisfies
the *old* `IsCompletelyPositiveOnMatrices`: for a tuple `aᵢ = (zᵢ, wᵢ)` the
double sum collapses to `Re ⟪U, (½ + N) U⟫ + Re ⟪V, (½ − N) V⟫` with
`U = ∑ zᵢ Wᵢ` and `V = ∑ wᵢ Wᵢ`, and each term is `½‖·‖²` because `N`
contributes nothing to a real part.  It fails the reality clause, which is the
point.  Yet **both** clauses of `UCPContractive` fail for it:
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

**No inhabitant of `UCPContractive` is constructed here, and none of
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
    (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
      (starRingEnd ℂ) (w i x) * φ (star (a i) * a j) x y * w j y).im = 0
      ∧ 0 ≤ (∑ i : Fin m, ∑ j : Fin m, ∑ x : Y, ∑ y : Y,
        (starRingEnd ℂ) (w i x) * φ (star (a i) * a j) x y * w j y).re

/-- The zero map is completely positive: every form vanishes.  A smoke test on
the orientation of the inequality and on the reality clause, nothing more. -/
theorem isCompletelyPositiveOnMatrices_zero (Y : FiniteModel) :
    IsCompletelyPositiveOnMatrices Y (fun _ : A ↦ (0 : Matrix Y Y ℂ)) := by
  intro m a w
  constructor <;> simp

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
  simpa using (h 1 (fun _ ↦ a) (fun _ ↦ w)).2

/-- **The form is real**, which is the clause the predicate was missing until
2026-08-19 and the one that makes it say complete positivity.

Without it the predicate constrains only the Hermitian part of each
`φ (a⋆ a)`: writing a matrix as `H + iK` with both Hermitian,
`Re ⟪w, T w⟫ = ⟪w, H w⟫`, so an anti-Hermitian summand is invisible.  The
module docstring carries the two-by-two unital map that satisfies the weakened
form and is neither `⋆`-preserving nor contractive; it is the reason
`UCPContractive` could not be discharged, and the reason the clause
is here. -/
theorem IsCompletelyPositiveOnMatrices.form_im {Y : FiniteModel}
    {φ : A → Matrix Y Y ℂ} (h : IsCompletelyPositiveOnMatrices Y φ) (a : A)
    (w : Y → ℂ) :
    (∑ x : Y, ∑ y : Y,
      (starRingEnd ℂ) (w x) * φ (star a * a) x y * w y).im = 0 := by
  simpa using (h 1 (fun _ ↦ a) (fun _ ↦ w)).1

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

/-! ## The form at a pair of `δ`-vectors -/

/-- The vector that is `1` at `q` and `0` elsewhere.

Public since 2026-08-19: `Analysis.QuasidiagonalTraceProperties` reads the
complete-positivity clause at a *single* `δ`-vector to see that the diagonal
entries of `φ (x⋆x)` are nonnegative reals, which is how a quasidiagonal trace
is shown to be positive. -/
def diracVec (Y : FiniteModel) (q : Y) : Y → ℂ :=
  fun x ↦ if x = q then 1 else 0

/-- The form of a single matrix at a pair of `δ`-vectors is the matrix entry. -/
theorem form_diracVec (Y : FiniteModel) (M : Matrix Y Y ℂ) (r s : Y) :
    ∑ x : Y, ∑ y : Y,
      (starRingEnd ℂ) (diracVec Y r x) * M x y * diracVec Y s y = M r s := by
  have hy : ∀ x : Y, ∑ y : Y,
      (starRingEnd ℂ) (diracVec Y r x) * M x y * diracVec Y s y
        = (starRingEnd ℂ) (diracVec Y r x) * M x s := by
    intro x
    have hterm : ∀ y : Y,
        (starRingEnd ℂ) (diracVec Y r x) * M x y * diracVec Y s y
          = if y = s then (starRingEnd ℂ) (diracVec Y r x) * M x y else 0 := by
      intro y
      by_cases hys : y = s <;> simp [diracVec, hys]
    rw [Finset.sum_congr rfl fun y _ ↦ hterm y]
    simp
  rw [Finset.sum_congr rfl fun x _ ↦ hy x]
  have hterm : ∀ x : Y,
      (starRingEnd ℂ) (diracVec Y r x) * M x s
        = if x = r then M x s else 0 := by
    intro x
    by_cases hxr : x = r <;> simp [diracVec, hxr]
  rw [Finset.sum_congr rfl fun x _ ↦ hterm x]
  simp

/-- **Complete positivity at a two-element tuple, read at one pair of entries.**
The four-term scalar is real. -/
private theorem cpForm_two_im {Y : FiniteModel} {φ : A → Matrix Y Y ℂ}
    (hcp : IsCompletelyPositiveOnMatrices Y φ) (a₀ a₁ : A) (r s : Y) :
    (φ (star a₀ * a₀) r r + φ (star a₀ * a₁) r s
      + φ (star a₁ * a₀) s r + φ (star a₁ * a₁) s s).im = 0 := by
  have h := (hcp 2 ![a₀, a₁] ![diracVec Y r, diracVec Y s]).1
  simpa [Fin.sum_univ_two, form_diracVec, add_assoc] using h

/-! ## The three readings -/

/-- **A unital completely positive map into a matrix algebra preserves
adjoints.**  This is the `map_star` clause of
`Quasidiagonal.UCPContractive`, proved. -/
theorem ucp_map_star {Y : FiniteModel} (φ : A →ₗ[ℂ] Matrix Y Y ℂ)
    (h1 : φ 1 = 1) (hcp : IsCompletelyPositiveOnMatrices Y ⇑φ) (b : A) :
    φ (star b) = (φ b)ᴴ := by
  ext s r
  set α : ℂ := φ b r s with hα
  set β : ℂ := φ (star b) s r with hβ
  set γ : ℂ := φ (star b * b) s s with hγ
  -- the tuple `(0, b)`: only the last entry survives
  have hzero : γ.im = 0 := by
    have h := cpForm_two_im hcp 0 b r s
    simpa [hγ] using h
  -- the tuple `(1, b)`
  have hone : (1 + α + β + γ).im = 0 := by
    have h := cpForm_two_im hcp 1 b r s
    simpa [h1, hα, hβ, hγ, Matrix.one_apply_eq] using h
  -- the tuple `(1, i • b)`
  have hI : (1 + Complex.I * α - Complex.I * β + γ).im = 0 := by
    have h := cpForm_two_im hcp 1 (Complex.I • b) r s
    have e₁ : star (1 : A) * (Complex.I • b) = Complex.I • b := by
      simp
    have e₂ : star (Complex.I • b) * (1 : A) = (-Complex.I) • star b := by
      simp [star_smul]
    have e₃ : star (Complex.I • b) * (Complex.I • b) = star b * b := by
      simp [star_smul, smul_smul, Complex.I_mul_I]
    rw [e₁, e₂, e₃] at h
    simpa [h1, hα, hβ, hγ, Matrix.one_apply_eq, map_smul, sub_eq_add_neg,
      neg_mul] using h
  -- the two readings, as real equations
  have him : β.im = -α.im := by
    simp only [Complex.add_im, Complex.one_im] at hone
    linarith [hzero, hone]
  have hre : β.re = α.re := by
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.one_im] at hI
    linarith [hzero, hI]
  -- and the conclusion, entry by entry
  have : β = (starRingEnd ℂ) α := by
    apply Complex.ext
    · simpa using hre
    · simpa using him
  simpa [hβ, hα, Matrix.conjTranspose_apply] using this

/-! ## The one remaining property of a ucp map, as a typed input -/

/-- **The one standard fact about unital completely positive maps into
matrices that this development still assumes**: such a map is a contraction.

It had a companion until 2026-08-19 -- that such a map is `⋆`-preserving --
and that companion is now `ucp_map_star`, proved above from the reality clause
of `IsCompletelyPositiveOnMatrices` at two-element tuples, with no dilation and
no C⋆-theory.  What is left is the norm bound, and the classical route to it is
Stinespring's theorem: a ucp map is the compression `V⋆ π(·) V` of a
`⋆`-representation along an isometry (Stinespring, *Positive functions on
C⋆-algebras*, Proc. Amer. Math. Soc. **6** (1955), 211--216; see also
Brown--Ozawa, *C⋆-algebras and Finite-Dimensional Approximations*, Chapter 1),
hence contractive.  The Kadison--Schwarz inequality for two-positive maps is
the other route.

**Why it is not a field of `QuasidiagonalTraceModel`.**  That structure is the
literal conclusion of Tikuisis--White--Winter.  Adding a clause to it would
make the theorem this repository *assumes* stronger than the theorem the
literature *proves*, which is the wrong direction for an input; and it would
make the transcription harder to check against the paper.  Kept separate, the
fact appears in the type of every theorem that uses it and is visible to
`scripts/check_non_mf_unconditional.py --audit-corpus` under its own name.

**This is dischargeable and TWW is not.**  Half of it has been discharged; see
the module docstring for why neither half could have been until the
complete-positivity predicate gained its reality clause, and for the two-by-two
map that shows the weakened predicate implies neither property.

**The other half exists too, at a different target.**
`CStarExactness.IsCompletelyPositive.norm_apply_le_of_unital`
(`Analysis/CStarUnitalCPContractive`) proves exactly this bound for a unital
completely positive `φ : A →ₗ[ℂ] (H →L[ℂ] H)`, off the repository's own
Stinespring dilation.  What separates it from an inhabitant of this structure
is the bridge the original note called steps (i) and (ii), and *only* that:

* (i) form-sense complete positivity here, now that it constrains the whole
  form rather than its real part, into `CStarExactness.IsCompletelyPositive`
  for the target `EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ Y`;
* (ii) the `⋆`-algebra identification of `Matrix Y Y ℂ` with that operator
  algebra, isometrically -- which is what the scoped
  `Matrix.Norms.L2Operator` instance is, so the norms already agree by
  definition rather than by a theorem.

Neither is a citation.  No inhabitant is constructed here yet.

It is a structure rather than a bare implication for the same reason
`QuasidiagonalMF.AmenableMFInput` is: consuming it then leaves a visible
binder in the type of every theorem that does, and the name is picked up by
`scripts/check_non_mf_unconditional.py --audit-corpus` as an assumed and
uninhabited one. -/
structure UCPContractive : Prop where
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

The `⋆` clause is now discharged outright by `ucp_map_star`; the boundedness
clause still enters through the explicit input `hucp`, so this theorem's type
records exactly what the passage from TWW's conclusion to Shulman's hypothesis
still costs in a development that has not formalized Stinespring's dilation
for matrix targets -- one inequality, no longer two facts. -/
def QuasidiagonalTraceModel.toMFTraceModel {τ : A → ℂ}
    (hucp : UCPContractive.{u}) (M : QuasidiagonalTraceModel τ) :
    ShulmanTrace.MFTraceModel τ where
  space := M.space
  map n := ⇑(M.map n)
  tendsto_mul := M.tendsto_mul
  tendsto_linear l m a b := ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
    simp only [map_add, map_smul, add_sub_cancel_left, sub_self, norm_zero]
  tendsto_star a := ShulmanTrace.tendsto_zero_of_eq_zero fun n ↦ by
    simp only [ucp_map_star (M.map n) (M.map_one n) (M.completelyPositive n) a,
      sub_self, norm_zero]
  bounded a := ⟨‖a‖, fun n ↦ hucp.norm_le A inferInstance (M.space n)
    (M.map n) (M.map_one n) (M.completelyPositive n) a⟩
  tendsto_trace := M.tendsto_trace

/-- The proposition-level form: a quasidiagonal trace is an MF trace. -/
theorem isMFTrace_of_isQuasidiagonalTrace {τ : A → ℂ}
    (hucp : UCPContractive.{u}) (h : IsQuasidiagonalTrace τ) :
    ShulmanTrace.IsMFTrace τ := by
  obtain ⟨M⟩ := h
  exact ⟨M.toMFTraceModel hucp⟩

end

end Quasidiagonal
end GroupApproximation
