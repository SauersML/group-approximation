import GroupApproximation.BooneHigman.Metabelian.VdKInjDirectTrans
import GroupApproximation.BooneHigman.Metabelian.VdKStabEndpoint
import GroupApproximation.BooneHigman.Metabelian.VdKRowCoreXEquiv
import GroupApproximation.BooneHigman.Metabelian.ElemFPVdKHighWire
import GroupApproximation.Meta.AxiomGuard

/-!
# Injective stability of `K₂` with row transitivity discharged

Lane `bh-met-91e`, wiring.  `VdKInjDirectTrans.lean` proves, for every commutative `R` with
`sr(R) ≤ r`, that `St_{m+1}(R)` acts transitively on unimodular rows of length `m + 1 > r`
(`vdkInjDirect_rowTransitive_of_stableRange`).  This is the first ingredient of van der Kallen's
elementary proof of injective stability.

## Residual: `vdkInjDirect_TransitiveInjStatement`

**LOUD: the residual is logically EQUIVALENT to `vdkStab_InjStabStatement`**
(`vdkInjDirect_transitive_iff_injStab`).  It is not strictly weaker, because its extra
hypothesis `vdkInjDirect_RowTransitive R r` is now a theorem.  It is strictly smaller only in
**proof content**: a proof of it may use transitivity on unimodular rows for free.  What is
left is the part of van der Kallen's argument that has no matrix-level shortcut:

* build the `St_{n+1}(R)`-set of unimodular rows and the coset structure on `St_{n+1}(R)`;
* identify the stabiliser of `e_last` with the parabolic `St_n(R) ⋉ Rⁿ`;
* show that `ker(K₂(n, R) → K₂(n + 1, R))` is trivial.

For the last step, no statement about `E_{n+1}(R)` or about rows can suffice: `K₂` is the
kernel of `St → E`.  So a residual that does not mention Steinberg words is necessarily either
equivalent to the target or false.

**Truth.**  Van der Kallen's theorem gives injectivity of `K₂(N, R) → K₂(N + 1, R)` for
`N ≥ sr(R) + 2`.  Here `N = r + 3` is used, one step more.  It is not assumed anywhere: it is
the open residual.  The route does not use `polyK2StabRangeDiag_of_vdkRowExtension`, row
extension, specialization, or homotopy invariance.

## Endpoints

* `vdkInjDirect_injStab_of_transitive : … → vdkStab_InjStabStatement` (general `R`).
* `vdkInjDirect_diag_of_transitive : … → vdkInj_DiagStatement`, via
  `vdkRowCoreX_diag_iff_injective.mpr`.
* `vdkInjDirect_vdkRowExt : … → VdKRowExtensionStatement`, via
  `vdkHighWire_vdkRowExt_of_diag`.
* `Envelope.vdkInjDirect_finitelyPresentedMetabelian_of_six`: this is
  `vdkHighWire_finitelyPresentedMetabelian_of_six` with `hdiag` replaced by the residual.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Residual** (lane `bh-met-91e`): injective stability of `K2Stab (r + 3) R` for commutative
`R` with `sr(R) ≤ r`, where elementary transitivity on unimodular rows may be used as a given.
LOUD: this is logically equivalent to `vdkStab_InjStabStatement`
(`vdkInjDirect_transitive_iff_injStab`).  It is smaller only in proof content, since the
transitivity hypothesis is discharged by `vdkInjDirect_rowTransitive_of_stableRange`. -/
def vdkInjDirect_TransitiveInjStatement : Prop :=
  ∀ (R : Type) [CommRing R] (r : ℕ), vdkStab_StableRangeLE R r →
    vdkInjDirect_RowTransitive R r → Function.Injective (K2Stab (r + 3) R)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_TransitiveInjStatement

/-- **Endpoint** (general `R`): injective stability of `K₂` from the residual. -/
theorem vdkInjDirect_injStab_of_transitive (h : vdkInjDirect_TransitiveInjStatement) :
    vdkStab_InjStabStatement := by
  intro R _ r N hsr hN
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 3 := ⟨N - 3, by omega⟩
  have hm : vdkStab_StableRangeLE R m := vdkStab_stableRangeLE_mono hsr (by omega)
  exact h R m hm (vdkInjDirect_rowTransitive_of_stableRange hm)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_injStab_of_transitive

/-- **Strength** (LOUD): the residual is equivalent to `vdkStab_InjStabStatement`. -/
theorem vdkInjDirect_transitive_iff_injStab :
    vdkInjDirect_TransitiveInjStatement ↔ vdkStab_InjStabStatement :=
  ⟨vdkInjDirect_injStab_of_transitive, fun h R _ r hsr _ => h R r (r + 3) hsr le_rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_transitive_iff_injStab

/-- **Endpoint**: the diagonal statement from the residual, through
`vdkRowCoreX_diag_iff_injective`, at `R = F_p[s_1, …, s_k]`. -/
theorem vdkInjDirect_diag_of_transitive (h : vdkInjDirect_TransitiveInjStatement) :
    vdkInj_DiagStatement :=
  vdkRowCoreX_diag_iff_injective.mpr fun p _ k r _ hsr =>
    h (MvPolynomial (Fin k) (ZMod p)) r hsr (vdkInjDirect_rowTransitive_of_stableRange hsr)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_diag_of_transitive

/-- **Endpoint**: `VdKRowExtensionStatement` from the residual. -/
theorem vdkInjDirect_vdkRowExt (h : vdkInjDirect_TransitiveInjStatement) :
    VdKRowExtensionStatement :=
  vdkHighWire_vdkRowExt_of_diag (vdkInjDirect_diag_of_transitive h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjDirect_vdkRowExt

end GroupApproximation.BooneHigman.Metabelian.ElemFP

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

/-- `vdkHighWire_finitelyPresentedMetabelian_of_six` with `hdiag` replaced by the residual
`ElemFP.vdkInjDirect_TransitiveInjStatement`. -/
theorem vdkInjDirect_finitelyPresentedMetabelian_of_six
    (hH : Absorption.SuslinLocalHorrocksStatement)
    (hres : ElemFP.vdkInjDirect_TransitiveInjStatement)
    (hloc : ElemFP.PolyK2CubeNilLocalStatement)
    (hgen : ElemFPCharZero.CharZeroK2PosStabGenStatement)
    (hcube : ElemFPCharZero.CharZeroK2CubeGapPosStatement)
    (hswap : HigmanVSwapSectionStatement) : FinitelyPresentedMetabelianStatement :=
  vdkHighWire_finitelyPresentedMetabelian_of_six hH
    (ElemFP.vdkInjDirect_diag_of_transitive hres) hloc hgen hcube hswap

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.Envelope.vdkInjDirect_finitelyPresentedMetabelian_of_six

end GroupApproximation.BooneHigman.Metabelian.Envelope
