import GroupApproximation.Analysis.QuasidiagonalTraceLocal
import GroupApproximation.Analysis.KirchbergRordamCorona
import GroupApproximation.Meta.AxiomGuard

/-!
# Lifting criterion, coordinate form

A ucp lift of a corona homomorphism with an `ω`-trace clause makes the trace
quasidiagonal.

Lane `nm-tww-09` (region nm-tww, tranche B: TWW-free infrastructure for Schafhauser's
proof of Tikuisis--White--Winter).

The last step of the trace-kernel route is this. We have unital completely positive
matrix maps `φₙ : A → M_{X n}`. Their assembled sequence induces a map into the corona
`ℓ∞(M_{X n}) / c₀(M_{X n})`, and that map is multiplicative on the nose. Also,
`lim_ω tr φₙ(a) = τ(a)` along a free ultrafilter `ω`. Then `τ` is quasidiagonal.

## Truth check

The corona product identity says `‖φₙ(ab) − φₙ(a)φₙ(b)‖ → 0` along `cofinite`, and so
along `ω`. For a finite `F ⊆ A` and `ε > 0` there are finitely many conditions, each
holding on an `ω`-large set, and their intersection is nonempty. One index `n` then gives
the local form of quasidiagonality. The local form becomes the sequence form on a
separable algebra (`Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`).

## Route (differs from the cartographer's note, and is shorter)

The lane note suggests passing to an `atTop` subsequence with
`UltrafilterDiagonalExtraction` and then `isQuasidiagonalTrace_of_coronaModel`. That needs
a countable dense set and continuity of `τ` before extraction. Going through the
*local* form avoids both. The finite intersection of `ω`-large sets is nonempty. The
diagonal argument, and the Lipschitz bound on `τ` it needs, are already proved
unconditionally in `Analysis/QuasidiagonalTraceLocal.lean`. Nuclearity is **not** used
here. It is used only to *produce* the coordinates (lane `nm-tww-08`, see
`LiftCriterion/Statement.lean`).

Nothing in this file is conditional.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TWWLanes
namespace LiftCriterion

open Filter Matrix Quasidiagonal
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- **Coordinate lifting criterion, local form.**  Unital completely positive matrix
maps `φₙ` are given. Their assembled bounded sequence `seq` is multiplicative in the
cofinite corona. Their normalized traces converge to `τ` along a free ultrafilter `ω`.
Then `τ` is a locally quasidiagonal trace. -/
theorem isLocallyQuasidiagonalTrace_of_coronaCoordinates {τ : A → ℂ}
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (φ : ∀ n : ℕ, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hone : ∀ n : ℕ, φ n 1 = 1)
    (hcp : ∀ n : ℕ, IsCompletelyPositiveOnMatrices (X n) ⇑(φ n))
    (seq : A → BoundedMatrixSequence (fun n => X n))
    (hseq : ∀ (a : A) (n : ℕ), seq a n = φ n a)
    (hmul : ∀ a b : A,
      normMatrixCStarCoronaMk (fun n => X n) (seq a)
          * normMatrixCStarCoronaMk (fun n => X n) (seq b)
        = normMatrixCStarCoronaMk (fun n => X n) (seq (a * b)))
    (htr : ∀ a : A,
      Tendsto (fun n => normTrace (X n) (φ n a)) (ω : Filter ℕ) (nhds (τ a))) :
    IsLocallyQuasidiagonalTrace τ := by
  intro F ε hε
  have hωtop : (ω : Filter ℕ) ≤ atTop := hω.trans_eq Nat.cofinite_eq_atTop
  have hmulω : ∀ x ∈ F, ∀ y ∈ F, ∀ᶠ n in (ω : Filter ℕ),
      ‖φ n (x * y) - φ n x * φ n y‖ < ε := by
    intro x _ y _
    have h := KirchbergRordam.tendsto_norm_sub_mul_of_corona_mul
      (X := fun n => (X n).carrier) (u := seq x) (v := seq y)
      (w := seq (x * y)) (hmul x y)
    have h' : Tendsto (fun n => ‖φ n (x * y) - φ n x * φ n y‖) atTop (nhds 0) :=
      h.congr fun n => by simp only [hseq]
    exact TracialUltraproduct.eventually_lt_of_tendsto_zero (h'.mono_left hωtop) hε
  have htrω : ∀ x ∈ F, ∀ᶠ n in (ω : Filter ℕ),
      ‖τ x - normTrace (X n) (φ n x)‖ < ε := by
    intro x _
    filter_upwards [Metric.tendsto_nhds.mp (htr x) ε hε] with n hn
    rwa [dist_eq_norm, norm_sub_rev] at hn
  have h1 : ∀ᶠ n in (ω : Filter ℕ),
      ∀ x ∈ F, ∀ y ∈ F, ‖φ n (x * y) - φ n x * φ n y‖ < ε :=
    (Filter.eventually_all_finset F).mpr fun x hx =>
      (Filter.eventually_all_finset F).mpr (hmulω x hx)
  have h2 : ∀ᶠ n in (ω : Filter ℕ),
      ∀ x ∈ F, ‖τ x - normTrace (X n) (φ n x)‖ < ε :=
    (Filter.eventually_all_finset F).mpr htrω
  obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
  exact ⟨X n, φ n, hone n, hcp n, fun x hx y hy => (hn1 x hx y hy).le,
    fun x hx => (hn2 x hx).le⟩

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.isLocallyQuasidiagonalTrace_of_coronaCoordinates

/-- **Coordinate lifting criterion, sequence form.**  On a separable algebra the same data
make `τ` a quasidiagonal trace in the sequence sense (`Quasidiagonal.IsQuasidiagonalTrace`). -/
theorem isQuasidiagonalTrace_of_coronaCoordinates [TopologicalSpace.SeparableSpace A]
    {τ : A → ℂ}
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (φ : ∀ n : ℕ, A →ₗ[ℂ] Matrix (X n) (X n) ℂ)
    (hone : ∀ n : ℕ, φ n 1 = 1)
    (hcp : ∀ n : ℕ, IsCompletelyPositiveOnMatrices (X n) ⇑(φ n))
    (seq : A → BoundedMatrixSequence (fun n => X n))
    (hseq : ∀ (a : A) (n : ℕ), seq a n = φ n a)
    (hmul : ∀ a b : A,
      normMatrixCStarCoronaMk (fun n => X n) (seq a)
          * normMatrixCStarCoronaMk (fun n => X n) (seq b)
        = normMatrixCStarCoronaMk (fun n => X n) (seq (a * b)))
    (htr : ∀ a : A,
      Tendsto (fun n => normTrace (X n) (φ n a)) (ω : Filter ℕ) (nhds (τ a))) :
    IsQuasidiagonalTrace τ :=
  isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace inferInstance
    (isLocallyQuasidiagonalTrace_of_coronaCoordinates X ω hω φ hone hcp seq hseq hmul htr)

#audit_axioms GroupApproximation.Manuscript.NonMF.TWWLanes.LiftCriterion.isQuasidiagonalTrace_of_coronaCoordinates

end

end LiftCriterion
end TWWLanes
end NonMF
end Manuscript
end GroupApproximation
