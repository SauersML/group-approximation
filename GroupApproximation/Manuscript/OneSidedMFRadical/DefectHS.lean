import GroupApproximation.Sofic.OpToHSShadowResidual

/-!
# Hilbert--Schmidt invisibility of compression defects

This module is the exact manuscript-facing endpoint for
`non_mf_groups_exist.tex`, Corollary `cor:defect-hs`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

/-- **Corollary `cor:defect-hs`.** If a property-`(T)` subgroup is compressed
one-sidedly and `c` centralizes it, every displayed compression commutator is
in the operator-to-Hilbert--Schmidt shadow residual. -/
def CompressionDefectHSInvisible : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} L →
    ∀ compressor : G,
      (∀ ell ∈ L, compressor * ell * compressor⁻¹ ∈ L) →
      ∀ centralizer : G,
        (∀ ell ∈ L, Commute centralizer ell) →
        ∀ ell ∈ L,
          ⁅compressor * centralizer * compressor⁻¹, ell⁆ ∈
            opToHSShadowResidual G

/-- Closed proof of the manuscript's Hilbert--Schmidt defect corollary. -/
theorem manuscriptCompressionDefectHSInvisible :
    CompressionDefectHSInvisible := by
  intro G _ L hT compressor hcompressor centralizer hcentralizer ell hell
  let C : KazhdanCompressionCore L G :=
    { iota := L.subtype
      t := compressor
      c := centralizer
      kazhdan := hT
      compresses := by
        intro gamma
        exact ⟨⟨compressor * gamma * compressor⁻¹,
          hcompressor gamma gamma.property⟩, rfl⟩
      comm_c := fun gamma ↦ hcentralizer gamma gamma.property }
  let gamma : L := ⟨ell, hell⟩
  rw [mem_opToHSShadowResidual_iff]
  intro B U hcof
  simpa [C, gamma, KazhdanCompressionCore.transported] using
    KazhdanCompressionCore.compressionDefects_eq_one_in_hyperlinearHom
      C B hcof gamma

end OneSidedMFRadical
end Manuscript
end GroupApproximation
