import GroupApproximation.BooneHigman.Metabelian.VdKInjCosetRows
import GroupApproximation.Meta.AxiomGuard

/-!
# Step A in the stable range, and what it does not give

Lane `bh-met-91j`, last file.

* `vdkInjCoset_RowStabStatement`: Step A (`rowStab ≤ P`) at every level `N ≥ sr(R) + 3`.
* `vdkInjCoset_k2StabSurjective_of_rowStabStatement`: it gives surjective `K₂` stability,
  `K2Stab N R` onto, in the same range (**proved** reduction).
* `vdkInjCoset_rowEquiv_of_rowStabStatement`: it gives the orbit–stabiliser bijection
  `P \ St_{N+1}(R) ≃ Um_{N+1}(R)` (**proved** reduction, using proved elementary transitivity).

LOUD (truth check, lane `bh-met-91j`).
* `vdkInjCoset_RowStabStatement` is **TRUE**.  By `vdkInjCoset_rowStabAt_iff`, it amounts to
  van der Kallen's surjective `K₂` stability (`n ≥ sr + 1`) plus the block-diagonal part of
  Bass–Vaserstein `K₁` injective stability (`GL_n ∩ E_{n+1} = E_n` for `n ≥ sr + 1`).
* It is **not** a residual for injectivity.  It is neither weaker nor stronger than
  `vdkStab_InjStabStatement`: it is independent of it, being a surjective-type statement.
  Step B of the lane ("Step A ⟹ `K2Stab` injective") is **not** a valid deduction.  Step A
  describes `ker(St_{N+1} → rows)`, not `ker(K₂(N) → K₂(N+1))`.
* The injectivity gap is therefore **unchanged**.  It is still `vdkInjDirect_TransitiveInjStatement`
  (equivalently `vdkStab_InjStabStatement`, equivalently injectivity of `vdkRowPar`; see
  `vdkRowParInjective_iff_K2Stab_injective`).  No strictly weaker true residual for injectivity
  is isolated here.
* Nothing here assumes a relator-family statement (`VdKRowData`, `vdkDiag_RowCoreStatement`,
  the `VdKRowExt*` statements),
  a citation, dilation, excision, symbols or homotopy invariance.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Step A in the stable range**: for `sr(R) ≤ r` and `N ≥ r + 3`, every element of
`St_{N+1}(R)` fixing the row `e_last` lies in the parabolic image `colVec · stab(St_N(R))`.
TRUE (van der Kallen `K₂` surjective stability plus Bass–Vaserstein `K₁` injective stability),
but surjective-type: it does not imply injective stability (see the module docstring). -/
def vdkInjCoset_RowStabStatement : Prop :=
  ∀ (R : Type) [CommRing R] (r N : ℕ), vdkStab_StableRangeLE R r → r + 3 ≤ N →
    vdkInjCoset_RowStabAt N R

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_RowStabStatement

/-- **Proved reduction**: Step A in the stable range gives surjective `K₂` stability in the
same range. -/
theorem vdkInjCoset_k2StabSurjective_of_rowStabStatement (hA : vdkInjCoset_RowStabStatement)
    (R : Type) [CommRing R] (r N : ℕ) (hsr : vdkStab_StableRangeLE R r) (hN : r + 3 ≤ N) :
    Function.Surjective (K2Stab N R) :=
  vdkInjCoset_K2Stab_surjective_of_rowStabAt (hA R r N hsr hN)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_k2StabSurjective_of_rowStabStatement

/-- **Proved reduction**: Step A in the stable range identifies the parabolic cosets of
`St_{N+1}(R)` with the unimodular rows of length `N + 1`. -/
noncomputable def vdkInjCoset_rowEquiv_of_rowStabStatement (hA : vdkInjCoset_RowStabStatement)
    (R : Type) [CommRing R] (r N : ℕ) (hsr : vdkStab_StableRangeLE R r) (hN : r + 3 ≤ N) :
    VdKRowCoset N R ≃ {u : Fin (N + 1) → R // vdkStab_IsUnimodular u} :=
  vdkInjCoset_rowEquiv hsr (by omega) (hA R r N hsr hN)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCoset_rowEquiv_of_rowStabStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
