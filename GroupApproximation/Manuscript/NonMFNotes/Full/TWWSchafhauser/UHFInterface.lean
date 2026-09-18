import GroupApproximation.Analysis.QuasidiagonalTrace

/-!
# The universal UHF algebra `Q`: the interface

Lane `TWWSch3d5a` (work order `WO-TWWSchafhauser-3d-5`, part (a)).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), through
C. Schafhauser, *A new proof of the Tikuisis--White--Winter theorem*, J. reine
angew. Math. **759** (2020), 291--304, §4, which runs the obstruction argument
over the universal UHF algebra
`Q = lim (M_{1!} ⊂ M_{2!} ⊂ M_{3!} ⊂ ⋯)` (Glimm, Trans. AMS **95** (1960);
Davidson, *C⋆-algebras by example*, Ch. III).

This file fixes only the **API** that the compression step (part (b),
`ObstructionUHF.lean`) consumes, so that both halves can be written in parallel.
The construction is in `UHFConstruction*.lean`, and it ends in an inhabitant of
`UHFModel`.

`UHFModel Q` bundles, for a unital C⋆-algebra `Q`:

* `ι m : M_{m!} →⋆ₐ[ℂ] Q`, the unital inclusions of the building blocks;
* `expect m : Q →ₗ[ℂ] M_{m!}`, the conditional expectations (normalized partial
  traces), with `expect m ∘ ι m = id`;
* `expect m` is contractive in the operator norm of `M_{m!}`;
* `expect m` is completely positive in the form sense
  `Quasidiagonal.IsCompletelyPositiveOnMatrices`;
* the bimodule property `expect m (ι m a * x * ι m b) = a * expect m x * b`;
* the trace `trace : Q →ₗ[ℂ] ℂ` with `trace = normTrace ∘ expect m` for every `m`;
* the approximation property: `‖ι m (expect m x) - x‖ → 0` as `m → ∞`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter Matrix GroupApproximation.Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The `m`-th building block `M_{m!}` of the universal UHF algebra**, as a
finite model.  Its carrier is `Fin m.factorial`. -/
abbrev uhfLevel (m : ℕ) : FiniteModel :=
  ⟨Fin m.factorial, inferInstance, inferInstance⟩

@[simp] theorem card_uhfLevel (m : ℕ) : Fintype.card (uhfLevel m) = m.factorial := by
  show Fintype.card (Fin m.factorial) = m.factorial
  exact Fintype.card_fin _

/-- **The API of the universal UHF algebra** `Q = lim M_{m!}` that Schafhauser's
compression step uses (Crelle 759 (2020), §4).

* `ι m` is the unital inclusion `M_{m!} → Q`;
* `expect m` is the conditional expectation `Q → M_{m!}` (block average);
* `trace` is the tracial state of `Q`, equal to `normTrace ∘ expect m` for all `m`;
* `tendsto_ι_expect` says that the blocks exhaust `Q`. -/
structure UHFModel (Q : Type) [CStarAlgebra Q] where
  /-- The unital inclusions `M_{m!} → Q`. -/
  ι : ∀ m : ℕ, Matrix (uhfLevel m) (uhfLevel m) ℂ →⋆ₐ[ℂ] Q
  /-- The conditional expectations `Q → M_{m!}`. -/
  expect : ∀ m : ℕ, Q →ₗ[ℂ] Matrix (uhfLevel m) (uhfLevel m) ℂ
  /-- `expect m` is a left inverse of `ι m`. -/
  expect_ι : ∀ (m : ℕ) (a : Matrix (uhfLevel m) (uhfLevel m) ℂ), expect m (ι m a) = a
  /-- `expect m` is contractive (operator norm on `M_{m!}`). -/
  norm_expect_le : ∀ (m : ℕ) (x : Q), ‖expect m x‖ ≤ ‖x‖
  /-- `expect m` is completely positive, in the form sense. -/
  completelyPositive : ∀ m : ℕ, IsCompletelyPositiveOnMatrices (uhfLevel m) ⇑(expect m)
  /-- The bimodule property of a conditional expectation. -/
  expect_ι_mul_mul_ι : ∀ (m : ℕ) (a : Matrix (uhfLevel m) (uhfLevel m) ℂ) (x : Q)
    (b : Matrix (uhfLevel m) (uhfLevel m) ℂ),
    expect m (ι m a * x * ι m b) = a * expect m x * b
  /-- The tracial state of `Q`. -/
  trace : Q →ₗ[ℂ] ℂ
  /-- The trace factors through every conditional expectation. -/
  trace_eq : ∀ (m : ℕ) (x : Q), trace x = normTrace (uhfLevel m) (expect m x)
  /-- The building blocks exhaust `Q`. -/
  tendsto_ι_expect : ∀ x : Q,
    Tendsto (fun m : ℕ ↦ ‖ι m (expect m x) - x‖) atTop (nhds 0)

namespace UHFModel

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q)

/-- `expect m` is unital. -/
theorem expect_one (m : ℕ) : M.expect m 1 = 1 := by
  have h := M.expect_ι m 1
  rw [map_one] at h
  exact h

/-- `expect m` is multiplicative on the image of `ι m` (the special case of the
bimodule property that the compression step uses). -/
theorem expect_ι_mul_ι (m : ℕ) (a b : Matrix (uhfLevel m) (uhfLevel m) ℂ) :
    M.expect m (M.ι m a * M.ι m b) = a * b := by
  rw [← map_mul, M.expect_ι]

/-- The trace is unital. -/
theorem trace_one : M.trace 1 = 1 := by
  rw [M.trace_eq 0, M.expect_one]
  show Matrix.trace (1 : Matrix (Fin (Nat.factorial 0)) (Fin (Nat.factorial 0)) ℂ) /
    (Fintype.card (Fin (Nat.factorial 0)) : ℂ) = 1
  rw [Matrix.trace_one, Fintype.card_fin, Nat.factorial_zero]
  norm_num

end UHFModel

end

end GroupApproximation.Full.TWWSchafhauser
