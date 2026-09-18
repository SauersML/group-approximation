import GroupApproximation.Analysis.QuasidiagonalTraceLocal
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.UHFInterface
import GroupApproximation.Manuscript.NonMFNotes.Full.TWWSchafhauser.ObstructionUHFCP

/-!
# Compression from the universal UHF algebra to matrices

Lane `TWWSch3d5b` (work order `WO-TWWSchafhauser-3d-5`, part (b)).  Manuscript:
`non_mf_group_notes.tex`, `thm:fixed-radical-membership` (l.1376--1378), which
cites Tikuisis--White--Winter, *Quasidiagonality of nuclear C⋆-algebras*,
Ann. of Math. (2) **185** (2017), Theorem A, through C. Schafhauser, *A new proof
of the Tikuisis--White--Winter theorem*, J. reine angew. Math. **759** (2020),
291--304, §4.

Schafhauser runs the obstruction argument over the universal UHF algebra
`Q = lim M_{m!}`.  It ends with unital completely positive maps `φ_n : S → Q`
that are asymptotically multiplicative along an ultrafilter `ω` and whose traces
`tr_Q ∘ φ_n` converge to `τ` along `ω`.  This file proves the last step: such
maps make `τ` a locally quasidiagonal trace.

The proof runs as follows.  Fix a finite `F ⊆ S` and `ε > 0`.

1. Choose `n` in an `ω`-large set on which every multiplicative defect of `φ_n`
   on `F × F` is below `ε / 2` and every trace defect on `F` is below `ε`.
2. The blocks exhaust `Q` (`UHFModel.tendsto_ι_expect`).  So for the finitely
   many pairs `p = φ_n x`, `q = φ_n y` with `x, y ∈ F`, choose `m` with
   `‖ι_m E_m p · ι_m E_m q − p q‖ < ε / 2`.
3. The model is `ψ = E_m ∘ φ_n : S → M_{m!}`.
   * It is unital because `E_m 1 = 1`.
   * It is completely positive by `isCompletelyPositiveOnMatrices_comp_isCompletelyPositive`.
   * Multiplicativity: `E_m p · E_m q = E_m (ι_m E_m p · ι_m E_m q)` since `ι_m` is a
     homomorphism and `E_m ∘ ι_m = id`, and `E_m` is contractive.  Hence
     `‖ψ(xy) − ψ x ψ y‖ ≤ ‖φ_n(xy) − p q‖ + ‖ι_m E_m p · ι_m E_m q − p q‖ ≤ ε`.
   * The trace clause is exact, since `tr_Q = normTrace ∘ E_m`.

The algebra `Q` enters only through `UHFModel` (`UHFInterface.lean`, lane
`TWWSch3d5a`).  Nothing here is assumed: there is no input structure standing in
for a literature theorem, and `UHFFilterModel` is plain data about the maps `φ_n`.
-/

namespace GroupApproximation.Full.TWWSchafhauser

open Filter Matrix GroupApproximation.Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

namespace UHFModel

variable {Q : Type} [CStarAlgebra Q] (M : UHFModel Q)

/-- The blocks converge to every element of `Q`, as a limit in `Q`. -/
theorem tendsto_ι_expect_nhds (x : Q) :
    Tendsto (fun m : ℕ ↦ M.ι m (M.expect m x)) atTop (nhds x) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (M.tendsto_ι_expect x)

/-- **Products are approximated blockwise.**  Multiplication is continuous, so
`ι_m E_m p · ι_m E_m q → p q`. -/
theorem tendsto_norm_ι_mul_ι_sub (p q : Q) :
    Tendsto (fun m : ℕ ↦
      ‖M.ι m (M.expect m p) * M.ι m (M.expect m q) - p * q‖) atTop (nhds 0) :=
  tendsto_iff_norm_sub_tendsto_zero.1
    ((M.tendsto_ι_expect_nhds p).mul (M.tendsto_ι_expect_nhds q))

/-- **The multiplicative defect of `E_m` is controlled by the block approximation
of the product.**  `E_m p · E_m q = E_m (ι_m E_m p · ι_m E_m q)`, and `E_m` is
contractive. -/
theorem norm_expect_mul_sub_le (m : ℕ) (p q : Q) :
    ‖M.expect m (p * q) - M.expect m p * M.expect m q‖
      ≤ ‖M.ι m (M.expect m p) * M.ι m (M.expect m q) - p * q‖ := by
  rw [← M.expect_ι_mul_ι m (M.expect m p) (M.expect m q), ← map_sub (M.expect m),
    norm_sub_rev (M.ι m (M.expect m p) * M.ι m (M.expect m q)) (p * q)]
  exact M.norm_expect_le m _

end UHFModel

variable {Q : Type} [CStarAlgebra Q] {A : Type u} [CStarAlgebra A]

/-- **Ucp models into the universal UHF algebra along a filter.**  Unital
completely positive maps `φ_n : A → Q` whose multiplicative defects are null
along `l` and whose traces `tr_Q ∘ φ_n` converge to `τ` along `l`.  This is the
output of Schafhauser's obstruction argument (Crelle 759 (2020), §4) at `l = ω`. -/
structure UHFFilterModel (M : UHFModel Q) (τ : A → ℂ) (l : Filter ℕ) where
  /-- The maps `φ_n : A → Q`. -/
  map : ℕ → A →ₗ[ℂ] Q
  /-- Each `φ_n` is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each `φ_n` is completely positive. -/
  completelyPositive : ∀ n : ℕ, CStarExactness.IsCompletelyPositive (map n)
  /-- Multiplicativity along `l`, in the norm of `Q`. -/
  tendsto_mul : ∀ a b : A,
    Tendsto (fun n ↦ ‖map n (a * b) - map n a * map n b‖) l (nhds 0)
  /-- The traces `tr_Q ∘ φ_n` converge to `τ` along `l`. -/
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ a - M.trace (map n a)‖) l (nhds 0)

namespace UHFFilterModel

variable {M : UHFModel Q} {τ : A → ℂ} {l : Filter ℕ}

/-- **The compression theorem** (Schafhauser, Crelle 759 (2020), §4).  At a
nontrivial filter, ucp models into the universal UHF algebra `Q` compress to
matrix models: `τ` is a locally quasidiagonal trace. -/
theorem isLocallyQuasidiagonalTrace [l.NeBot] (N : UHFFilterModel M τ l) :
    IsLocallyQuasidiagonalTrace τ := by
  intro F ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hmul : ∀ᶠ n in l, ∀ x ∈ F, ∀ y ∈ F,
      ‖N.map n (x * y) - N.map n x * N.map n y‖ < ε / 2 := by
    refine (Filter.eventually_all_finset F).2 fun x _ ↦ ?_
    refine (Filter.eventually_all_finset F).2 fun y _ ↦ ?_
    exact TracialUltraproduct.eventually_lt_of_tendsto_zero (N.tendsto_mul x y) hε2
  have htr : ∀ᶠ n in l, ∀ x ∈ F, ‖τ x - M.trace (N.map n x)‖ < ε := by
    refine (Filter.eventually_all_finset F).2 fun x _ ↦ ?_
    exact TracialUltraproduct.eventually_lt_of_tendsto_zero (N.tendsto_trace x) hε
  obtain ⟨n, hn₁, hn₂⟩ := (hmul.and htr).exists
  have happrox : ∀ᶠ m in atTop, ∀ x ∈ F, ∀ y ∈ F,
      ‖M.ι m (M.expect m (N.map n x)) * M.ι m (M.expect m (N.map n y))
        - N.map n x * N.map n y‖ < ε / 2 := by
    refine (Filter.eventually_all_finset F).2 fun x _ ↦ ?_
    refine (Filter.eventually_all_finset F).2 fun y _ ↦ ?_
    exact TracialUltraproduct.eventually_lt_of_tendsto_zero
      (M.tendsto_norm_ι_mul_ι_sub (N.map n x) (N.map n y)) hε2
  obtain ⟨m, hm⟩ := happrox.exists
  refine ⟨uhfLevel m, M.expect m ∘ₗ N.map n, ?_, ?_, ?_, ?_⟩
  · show M.expect m (N.map n 1) = 1
    rw [N.map_one n, M.expect_one m]
  · exact isCompletelyPositiveOnMatrices_comp_isCompletelyPositive
      (M.completelyPositive m) (N.completelyPositive n)
  · intro x hx y hy
    show ‖M.expect m (N.map n (x * y))
        - M.expect m (N.map n x) * M.expect m (N.map n y)‖ ≤ ε
    have hsplit : M.expect m (N.map n (x * y))
          - M.expect m (N.map n x) * M.expect m (N.map n y)
        = M.expect m (N.map n (x * y) - N.map n x * N.map n y)
          + (M.expect m (N.map n x * N.map n y)
            - M.expect m (N.map n x) * M.expect m (N.map n y)) := by
      rw [map_sub (M.expect m), sub_add_sub_cancel]
    calc ‖M.expect m (N.map n (x * y))
          - M.expect m (N.map n x) * M.expect m (N.map n y)‖
        = ‖M.expect m (N.map n (x * y) - N.map n x * N.map n y)
          + (M.expect m (N.map n x * N.map n y)
            - M.expect m (N.map n x) * M.expect m (N.map n y))‖ := by
          rw [hsplit]
      _ ≤ ‖M.expect m (N.map n (x * y) - N.map n x * N.map n y)‖
          + ‖M.expect m (N.map n x * N.map n y)
            - M.expect m (N.map n x) * M.expect m (N.map n y)‖ :=
          norm_add_le _ _
      _ ≤ ‖N.map n (x * y) - N.map n x * N.map n y‖
          + ‖M.ι m (M.expect m (N.map n x)) * M.ι m (M.expect m (N.map n y))
            - N.map n x * N.map n y‖ :=
          add_le_add (M.norm_expect_le m _)
            (M.norm_expect_mul_sub_le m (N.map n x) (N.map n y))
      _ ≤ ε / 2 + ε / 2 := add_le_add (hn₁ x hx y hy).le (hm x hx y hy).le
      _ = ε := add_halves ε
  · intro x hx
    show ‖τ x - normTrace (uhfLevel m) (M.expect m (N.map n x))‖ ≤ ε
    rw [← M.trace_eq m]
    exact (hn₂ x hx).le

/-- **The compression theorem, sequence form.**  On a separable algebra the local
form upgrades to `Quasidiagonal.IsQuasidiagonalTrace`
(`Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`). -/
theorem isQuasidiagonalTrace [l.NeBot] (hsep : TopologicalSpace.SeparableSpace A)
    (N : UHFFilterModel M τ l) : IsQuasidiagonalTrace τ :=
  isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace hsep N.isLocallyQuasidiagonalTrace

end UHFFilterModel

/-- The existential form, for the consumer (`ObstructionUCT.lean`): some
ultrafilter carries ucp models into the universal UHF algebra inducing `τ`. -/
def HasUHFFilterModel (M : UHFModel Q) (τ : A → ℂ) : Prop :=
  ∃ ω : Ultrafilter ℕ, Nonempty (UHFFilterModel M τ (ω : Filter ℕ))

/-- **Ucp models into `Q` along some ultrafilter give a locally quasidiagonal
trace.** -/
theorem isLocallyQuasidiagonalTrace_of_hasUHFFilterModel {M : UHFModel Q} {τ : A → ℂ}
    (h : HasUHFFilterModel M τ) : IsLocallyQuasidiagonalTrace τ := by
  obtain ⟨ω, ⟨N⟩⟩ := h
  haveI : (ω : Filter ℕ).NeBot := Ultrafilter.neBot ω
  exact N.isLocallyQuasidiagonalTrace

end

end GroupApproximation.Full.TWWSchafhauser
