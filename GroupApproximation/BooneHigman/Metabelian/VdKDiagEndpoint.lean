import GroupApproximation.BooneHigman.Metabelian.VdKDiagCore
import GroupApproximation.BooneHigman.Metabelian.VdKInjDiag
import GroupApproximation.BooneHigman.Metabelian.VdKStabEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowCoset
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowParInjReadout
import GroupApproximation.Meta.AxiomGuard

/-!
# The diagonal residual from row data touching one base index

Lane `bh-met-90p`.  `vdkDiag_RowCoreStatement` asks, for `p` prime, `k > 0` and
`sr(F_p[s_1, …, s_k]) ≤ r`, for a nonempty `X` and a base index `o` carrying a
`vdkDiag_RowCore (r + 3) _ X o`: row roots on the free `P̃`-set whose relators are only imposed
when they touch `o`.

* `vdkDiag_diag_of_rowCore`: it implies `vdkInj_DiagStatement` (via `toRowData` and
  `VdKRowData.eq_one_of_K2Stab`).
* `vdkDiag_vdkRowExt_of_high_rowCore`: with the polynomial stable-range bound it gives
  `VdKRowExtensionStatement`.
* `vdkDiag_rowCore_of_injStab` (truth check): it follows from `vdkStab_InjStabStatement`.
* `vdkDiag_rowCore_iff_rowData`: it is equivalent to full row data at rank `r + 3`.

**Strength (LOUD).**  The residual is *not* weaker than `vdkInj_DiagStatement`: instance by
instance it gives injectivity of `K2Stab (r + 3)` on all of `K₂(r + 3, R_k)`, with no
specialization hypothesis on `u`.  What it removes is proof content relative to the repo's
only route to the diagonal statement (full `VdKRowData` at rank `r + 3`): the relators that do
not touch the base index are derived, not checked (`O(n)` / `O(n²)` instances in place of
`O(n²)` / `O(n³)`).  It is true, because it follows from van der Kallen's injective stability
(`vdkStab_InjStabStatement`).

**Note (LOUD).**  Describing the image of `vdkRowPar` as the stabilizer of the last basis
vector gives no injectivity: injectivity of `vdkRowPar` is equivalent to injectivity of
`K2Stab` (`vdkRowParInjective_of_K2Stab_injective` and its converse).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **The residual**: row data at rank `r + 3` over `F_p[s_1, …, s_k]`, with the relators only
imposed when they touch a base index `o`, whenever `sr ≤ r`. -/
def vdkDiag_RowCoreStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k r : ℕ, 0 < k →
    vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r →
    ∃ (X : Type) (o : Fin (r + 3)), Nonempty X ∧
      Nonempty (vdkDiag_RowCore (r + 3) (MvPolynomial (Fin k) (ZMod p)) X o)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_RowCoreStatement

/-- **Reduction**: the residual gives the diagonal statement. -/
theorem vdkDiag_diag_of_rowCore (h : vdkDiag_RowCoreStatement) : vdkInj_DiagStatement := by
  intro p hp k r hk hsr u _ hu
  obtain ⟨X, o, ⟨x₀⟩, ⟨C⟩⟩ := h p hp k r hk hsr
  exact C.toRowData.eq_one_of_K2Stab x₀ u hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_diag_of_rowCore

/-- **Wiring**: the polynomial stable-range bound and the residual give
`VdKRowExtensionStatement`. -/
theorem vdkDiag_vdkRowExt_of_high_rowCore (hA : vdkStab_PolyStableRangeHighStatement)
    (h : vdkDiag_RowCoreStatement) : VdKRowExtensionStatement :=
  vdkInj_vdkRowExt_of_high_diag hA (vdkDiag_diag_of_rowCore h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_vdkRowExt_of_high_rowCore

/-- **Truth check**: van der Kallen's injective stability gives the residual, through the
coset row data of `vdkRowDataOfInjective`. -/
theorem vdkDiag_rowCore_of_injStab (hB : vdkStab_InjStabStatement) :
    vdkDiag_RowCoreStatement := by
  intro p _ k r _ hsr
  have hK := hB (MvPolynomial (Fin k) (ZMod p)) r (r + 3) hsr le_rfl
  exact ⟨VdKRowCoset (r + 3) (MvPolynomial (Fin k) (ZMod p)), ⟨0, by omega⟩,
    ⟨Quotient.mk _ 1⟩,
    ⟨vdkDiag_RowCore.ofRowData
      (vdkRowDataOfInjective (vdkRowParInjective_of_K2Stab_injective hK)) _⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_rowCore_of_injStab

/-- **Strength**: the residual is equivalent to full row data at rank `r + 3`. -/
theorem vdkDiag_rowCore_iff_rowData : vdkDiag_RowCoreStatement ↔
    ∀ p : ℕ, p.Prime → ∀ k r : ℕ, 0 < k →
      vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r →
      ∃ X : Type, Nonempty X ∧ Nonempty (VdKRowData (r + 3) (MvPolynomial (Fin k) (ZMod p)) X) := by
  constructor
  · intro h p hp k r hk hsr
    obtain ⟨X, o, hX, ⟨C⟩⟩ := h p hp k r hk hsr
    exact ⟨X, hX, ⟨C.toRowData⟩⟩
  · intro h p hp k r hk hsr
    obtain ⟨X, hX, ⟨D⟩⟩ := h p hp k r hk hsr
    exact ⟨X, ⟨0, by omega⟩, hX, ⟨vdkDiag_RowCore.ofRowData D _⟩⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkDiag_rowCore_iff_rowData

end GroupApproximation.BooneHigman.Metabelian.ElemFP
