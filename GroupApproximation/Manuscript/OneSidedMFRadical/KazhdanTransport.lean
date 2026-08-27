import GroupApproximation.Sofic.PrintedReverseTransportRoute

/-!
# One-sided Kazhdan transport

This module is the exact manuscript-facing endpoint for
`non_mf_groups_exist.tex`, Theorem `thm:transport`. The two conjuncts are the
forward and inverse-conjugation limits printed in the theorem.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open Matrix
open KazhdanAsymptoticCommutant
open scoped Matrix.Norms.L2Operator

/-- **Theorem `thm:transport`.** A one-sided compressor of a property-`(T)`
subgroup transports every uniformly operator-bounded asymptotic
Hilbert--Schmidt commutant sequence in both conjugation directions. -/
def OneSidedKazhdanTransport : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} L →
    ∀ (B : OpAlmostRepresentation G)
      (x : ∀ n, Matrix (B.model n) (B.model n) ℂ),
      (∀ ell : L, HSSqVanishing B (fun n ↦
        x n - (B.map n ell : Matrix (B.model n) (B.model n) ℂ) *
          x n * (B.map n ell : Matrix (B.model n) (B.model n) ℂ)ᴴ)) →
      IsUniformlyBounded B x →
      ∀ compressor : G, compressor ∈ compressionSet L →
        IsAsymptoticCommutantOf B L.subtype
            (adjointSequence B compressor x) ∧
          IsAsymptoticCommutantOf B L.subtype
            (coadjointSequence B compressor x)

/-- Closed proof of both directions of the printed transport theorem. -/
theorem manuscriptOneSidedKazhdanTransport : OneSidedKazhdanTransport := by
  intro G _ L hT B x hx hbound compressor hcompressor
  have hcompressor' : compressor ∈ compressionSet L.subtype.range := by
    rwa [L.range_subtype]
  exact KazhdanAsymptoticCommutant.compressionSet_transport_both_printed
    B L.subtype hT x hx hbound hcompressor'

end OneSidedMFRadical
end Manuscript
end GroupApproximation
