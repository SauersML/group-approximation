import GroupApproximation.Manuscript.OneSidedMFRadical.CornerCoronaClass
import GroupApproximation.Analysis.CoronaProjectionLifting

/-!
# Retaining coordinates and passing to an omega matrix corona

These homomorphisms are independent of the corrected-corner projection-zero
assembly.  They package coordinate restriction in the cofinite corona and the
canonical quotient to any refining ultrafilter.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Filter
open PrintedCornerCompression

noncomputable section

/-- The canonical quotient from the cofinite corona to a finer omega corona. -/
noncomputable def cofiniteCoronaToOmega (Y : ℕ → Type*)
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)] [∀ n, Nonempty (Y n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    NormMatrixCStarCorona Y →⋆ₐ[ℂ]
      FilterMatrixCStarCorona Y (ω : Filter ℕ) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaStarLift Y cofinite
    (filterMatrixCStarCoronaQuotient Y (ω : Filter ℕ))
    (fun a ha ↦ (filterMatrixCStarCoronaMk_eq_zero_iff
      Y (ω : Filter ℕ) a).mpr (ha.mono_left hω))

@[simp] theorem cofiniteCoronaToOmega_mk (Y : ℕ → Type*)
    [∀ n, Fintype (Y n)] [∀ n, DecidableEq (Y n)] [∀ n, Nonempty (Y n)]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (a : BoundedMatrixSequence Y) :
    cofiniteCoronaToOmega Y ω hω (normMatrixCStarCoronaMk Y a) =
      filterMatrixCStarCoronaMk Y (ω : Filter ℕ) a :=
  rfl

/-- The coordinate-restriction ring homomorphism, bundled with its star and
complex-scalar compatibility. -/
noncomputable def coronaRestrictStar (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    NormMatrixCStarCorona (fun n ↦ X n) →⋆ₐ[ℂ]
      NormMatrixCStarCorona (fun k ↦ X (φ k)) := by
  change FilterMatrixCStarCorona (fun n ↦ X n) cofinite →⋆ₐ[ℂ]
    NormMatrixCStarCorona (fun k ↦ X (φ k))
  exact filterMatrixCStarCoronaLift (fun n ↦ X n) cofinite
    (restrictSeqCoronaQuotient X φ)
    (fun a ha ↦ restrictSeqCoronaQuotient_eq_zero_of_null X hφ a ha)

/-- Restrict coordinates and then pass from the cofinite corona to the chosen
refining ultrafilter. -/
noncomputable def retainedCoronaToOmega (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    NormMatrixCStarCorona (fun n ↦ X n) →⋆ₐ[ℂ]
      FilterMatrixCStarCorona (fun k ↦ X (φ k)) (ω : Filter ℕ) :=
  (cofiniteCoronaToOmega (fun k ↦ X (φ k)) ω hω).comp
    (coronaRestrictStar X φ hφ)

@[simp] theorem retainedCoronaToOmega_mk (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite)
    (a : BoundedMatrixSequence (fun n ↦ X n)) :
    retainedCoronaToOmega X φ hφ ω hω
        (normMatrixCStarCoronaMk (fun n ↦ X n) a) =
      filterMatrixCStarCoronaMk (fun k ↦ X (φ k)) (ω : Filter ℕ)
        (restrictSeq X φ a) := by
  have hrestrict :
      coronaRestrictStar X φ hφ
          (normMatrixCStarCoronaMk (fun n ↦ X n) a) =
        normMatrixCStarCoronaMk (fun k ↦ X (φ k))
          (restrictSeq X φ a) := by
    change filterMatrixCStarCoronaLift (fun n ↦ X n) cofinite
        (restrictSeqCoronaQuotient X φ)
        (fun b hb ↦ restrictSeqCoronaQuotient_eq_zero_of_null X hφ b hb)
        (filterMatrixCStarCoronaMk (fun n ↦ X n) cofinite a) = _
    rw [filterMatrixCStarCoronaLift_mk,
      restrictSeqCoronaQuotient_apply]
  rw [retainedCoronaToOmega, StarAlgHom.comp_apply, hrestrict,
    cofiniteCoronaToOmega_mk]

end

end OneSidedMFRadical
end Manuscript
end GroupApproximation
