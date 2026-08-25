import GroupApproximation.Manuscript.OneSidedMFRadical.DefectHS
import GroupApproximation.Manuscript.OneSidedMFRadical.FiniteDimensionalCommutant
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanProjectionOrder
import GroupApproximation.Manuscript.OneSidedMFRadical.KazhdanTransport
import GroupApproximation.Manuscript.OneSidedMFRadical.StableFiniteness

/-!
# Sentence-level closure for finite-dimensional and Kazhdan transport

This file gives unconditional named endpoints for every declarative proof
sentence retained in the manuscript sections `One-sided compression in finite
dimension` and `Kazhdan transport in normalized Hilbert--Schmidt norm`.

The printed proof now follows the route already checked by the imported files:
fixed submodules for the finite-dimensional commutant, coordinate correction
for stable finiteness, spectral projection and absorption identities inside the
target algebra for one-sided Kazhdan order, and the direct matrix transport
estimate for the compression commutator.  No maximal-group-C-star-algebra
factorization, faithful-representation bridge, or literature theorem is an
input to these endpoints.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u v w

/-- The proof sentences retained after `thm:commutant` are exactly the closed
finite-dimensional fixed-submodule theorem. -/
theorem manuscriptTransportFiniteDimensionalProofRoute :
    FiniteDimensionalCommutantRigidity :=
  manuscriptFiniteDimensionalCommutantRigidity

/-- The proof sentences retained in `lem:stable-finite` are exactly the closed
matrix-corona finiteness and projection-comparison package. -/
theorem manuscriptTransportStableFinitenessProofRoute :
    NormMatrixCoronaStableFinite :=
  manuscriptNormMatrixCoronaStableFinite

/-- The proof sentences retained in `lem:kazhdan-projection-order` use the
spectral projection constructed directly in the target and its two absorption
identities. -/
theorem manuscriptTransportProjectionOrderProofRoute :
    OneSidedKazhdanProjectionOrder :=
  manuscriptOneSidedKazhdanProjectionOrder

/-- The proof sentences retained in `thm:transport` are exactly the closed
two-direction transport theorem. -/
theorem manuscriptTransportProofRoute : OneSidedKazhdanTransport :=
  manuscriptOneSidedKazhdanTransport

/-- The proof sentences retained in `cor:defect-hs`, including inverse
replacement and multiplicative-defect control, are exactly the closed direct
matrix compression-defect theorem. -/
theorem manuscriptTransportDefectProofRoute : CompressionDefectHSInvisible :=
  manuscriptCompressionDefectHSInvisible

/-- One auditable proposition collecting the complete sentence-level surface
of the two transport sections. -/
def SentenceTransportClosure : Prop :=
  FiniteDimensionalCommutantRigidity.{u, v, w} ∧
    NormMatrixCoronaStableFinite ∧
    OneSidedKazhdanProjectionOrder ∧
    OneSidedKazhdanTransport ∧
    CompressionDefectHSInvisible

/-- Every declarative mathematical sentence retained in the two transport
sections has a closed unconditional Lean proof. -/
theorem manuscriptSentenceTransportClosure :
    SentenceTransportClosure.{u, v, w} := by
  exact ⟨manuscriptTransportFiniteDimensionalProofRoute,
    manuscriptTransportStableFinitenessProofRoute,
    manuscriptTransportProjectionOrderProofRoute,
    manuscriptTransportProofRoute,
    manuscriptTransportDefectProofRoute⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
