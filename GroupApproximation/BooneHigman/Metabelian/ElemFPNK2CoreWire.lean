import GroupApproximation.BooneHigman.Metabelian.ElemFPNK2CoreSlice
import GroupApproximation.BooneHigman.Metabelian.ElemFPNK2UnifyWire
import GroupApproximation.Meta.AxiomGuard

/-!
# The root with the slice `NK₂` residual

Lane `bh-met-90o`, wiring.

* `nk2Core_SliceStatement`: the slice residual `nk2Core_SliceOverStatement` over every
  `ℤ[1/m]`, `m ≥ 1`, and over every prime field `F_p`.
* `nk2Core_nk2UnifyCone_of_slice`: it gives the unified cone residual `nk2Unify_ConeStatement`
  (via `nk2Core_coneOver_of_sliceOver`, with `hres` from `czCubeLocal_exists_prime_mem` and
  `nk2Unify_hres_zmod`).
* `nk2Core_slice_of_nk2UnifyCone`: the converse.  **LOUD**: the two are logically equivalent;
  the slice residual is strictly smaller in proof content (see `ElemFPNK2CoreSlice`).
* `Envelope.nk2Core_finitelyPresentedMetabelian`: the root
  `Envelope.nk2Unify_finitelyPresentedMetabelian` with `hU` replaced by the slice residual.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.Metabelian.ElemFP

/-- **The slice residual** over every `ℤ[1/m]`, `m ≥ 1`, and over every prime field `F_p`. -/
def nk2Core_SliceStatement : Prop :=
  (∀ m : ℕ, 0 < m → nk2Core_SliceOverStatement (Localization.Away (m : ℤ))) ∧
    ∀ p : ℕ, p.Prime → nk2Core_SliceOverStatement (ZMod p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_SliceStatement

/-- **Endpoint (lane `bh-met-90o`).**  The slice residual gives the unified cone residual. -/
theorem nk2Core_nk2UnifyCone_of_slice (h : nk2Core_SliceStatement) :
    nk2Unify_ConeStatement :=
  ⟨fun m hm ↦ nk2Core_coneOver_of_sliceOver _
      (fun _ P hP ↦ czCubeLocal_exists_prime_mem (m : ℤ) P hP) (h.1 m hm),
    fun p hp ↦ nk2Core_coneOver_of_sliceOver _ (nk2Unify_hres_zmod p hp) (h.2 p hp)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_nk2UnifyCone_of_slice

/-- Conversely (**LOUD**: equivalence), the unified cone residual gives the slice residual. -/
theorem nk2Core_slice_of_nk2UnifyCone (h : nk2Unify_ConeStatement) :
    nk2Core_SliceStatement :=
  ⟨fun m hm ↦ nk2Core_sliceOver_of_coneOver _ (h.1 m hm),
    fun p hp ↦ nk2Core_sliceOver_of_coneOver _ (h.2 p hp)⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.nk2Core_slice_of_nk2UnifyCone

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- **The root with the slice `NK₂` residual.**  `nk2Unify_finitelyPresentedMetabelian` with the
unified cone residual `hU` replaced by the slice residual `nk2Core_SliceStatement`. -/
theorem nk2Core_finitelyPresentedMetabelian
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hvdk : ElemFP.VdKRowExtensionStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hU : ElemFPCharZero.nk2Core_SliceStatement)
    (hstab : ∀ m : ℕ, 0 < m →
      ElemFPCharZero.CZCubePosStabOverStatement (Localization.Away (m : ℤ)))
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  nk2Unify_finitelyPresentedMetabelian hH hvdk hgen
    (ElemFPCharZero.nk2Core_nk2UnifyCone_of_slice hU) hstab hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.nk2Core_finitelyPresentedMetabelian

end GroupApproximation.BooneHigman.Metabelian.Envelope
