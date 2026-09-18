import GroupApproximation.BooneHigman.Metabelian.VdKInjNeeded
import GroupApproximation.Meta.AxiomGuard

/-!
# The needed injective-stability statement: removal of the rank parameter

Lane `bh-met-90n`, part (2).  Target: `vdkInj_NeededStatement` (module `VdKInjNeeded`).

## Status of the attack

A proof of the needed statement is van der Kallen's injective stability theorem for the rings
`R_k = F_p[s_1, …, s_k]`.  The repo's Steinberg infrastructure reduces it to constructing row
data on a free `P̃`-set (`VdKRowData`, lane `bh-met-50`), which is itself equivalent to
injectivity at the given rank; the field case `k = 0` is proved (`vdkRowExt_fieldStab`) only
because there `K₂(N, F_p) = 0` (big Bruhat cell), an argument that has no analogue for `k > 0`.
The elementary (ESD-style) stable-range argument needs the full van der Kallen relation check
and was **not** closed here.

## What is proved

* `vdkInj_DiagStatement`: the needed statement at the diagonal rank `N = r + 3` only.
  **The isolated residual.**
* `vdkInj_needed_of_diag`: the diagonal gives the needed statement at every rank `N ≥ r + 3`.
  Given `N ≥ r + 3`, put `r' = N - 3 ≥ r`; `sr(R_k) ≤ r` gives `sr(R_k) ≤ r'`
  (`vdkStab_stableRangeLE_mono`), and the diagonal instance `(k, r')` has rank `r' + 3 = N`.
  The ring is not changed, so no specialization bookkeeping is needed.
* `vdkInj_diag_of_needed`: the converse (the residual is not logically stronger).
* `vdkInj_diag_of_injStab`: (B) gives the residual.
* `vdkInj_specPos_of_sr_of_diag`, `vdkInj_vdkRowExt_of_high_diag`: the wiring
  (A) + residual ⟹ `VdKRowExtSpecPosStatement`, (A, `k ≥ 2`) + residual ⟹
  `VdKRowExtensionStatement`.

## LOUD: strength

The residual is instancewise weaker than the needed statement (one rank per `(k, r)` instead of
all `N ≥ r + 3`) and strictly smaller in proof content (the rank parameter is discharged), but it
is logically equivalent to it (both directions proved).  It is strictly weaker than (B)
(`vdkInj_diag_of_injStab`; only the rings `R_k`, only elements killed by specializations).  It is
**not** an equivalent restatement of `VdKRowExtensionStatement`: it contains the low instances
`r ≤ k` (rank `r + 3 ≤ k + 3`), see module `VdKInjNeeded`; given (A) it is never weaker
than the target.

## Truth

Implied by (B) (`vdkInj_diag_of_injStab`), i.e. van der Kallen's injective stability for `K₂` in
the range `n ≥ sr + 2`, used at `n = r + 3 ≥ sr(R_k) + 3`.  True.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The isolated residual**: the needed statement at the diagonal rank `N = r + 3`.  For
`p` prime, `k > 0` and `sr(R_k) ≤ r`, an element of `K₂(r + 3, R_k)` that dies under every
specialization to fewer variables and under stabilization is trivial. -/
def vdkInj_DiagStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k r : ℕ, 0 < k →
    vdkStab_StableRangeLE (MvPolynomial (Fin k) (ZMod p)) r →
    ∀ u : K2n (r + 3) (MvPolynomial (Fin k) (ZMod p)),
      (∀ j : ℕ, j < k →
        ∀ ψ : MvPolynomial (Fin k) (ZMod p) →+* MvPolynomial (Fin j) (ZMod p),
          K2Map ψ u = 1) →
      K2Stab (r + 3) (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_DiagStatement

/-- **The reduction**: the diagonal residual gives the needed statement at every rank. -/
theorem vdkInj_needed_of_diag (h : vdkInj_DiagStatement) : vdkInj_NeededStatement := by
  intro p hp k r N hk hsr hN u hψ hu
  obtain ⟨r', rfl⟩ : ∃ r' : ℕ, N = r' + 3 := ⟨N - 3, by omega⟩
  exact h p hp k r' hk (vdkStab_stableRangeLE_mono hsr (by omega)) u hψ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_needed_of_diag

/-- The converse: the needed statement contains the diagonal residual. -/
theorem vdkInj_diag_of_needed (h : vdkInj_NeededStatement) : vdkInj_DiagStatement :=
  fun p hp k r hk hsr u hψ hu ↦ h p hp k r (r + 3) hk hsr le_rfl u hψ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_diag_of_needed

/-- (B) gives the diagonal residual: the residual is strictly weaker than (B). -/
theorem vdkInj_diag_of_injStab (hB : vdkStab_InjStabStatement) : vdkInj_DiagStatement :=
  vdkInj_diag_of_needed (vdkInj_needed_of_injStab hB)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_diag_of_injStab

/-- **Wiring**: (A) and the diagonal residual give `VdKRowExtSpecPosStatement`. -/
theorem vdkInj_specPos_of_sr_of_diag (hA : vdkStab_PolyStableRangeStatement)
    (h : vdkInj_DiagStatement) : VdKRowExtSpecPosStatement :=
  vdkInj_specPos_of_sr_of_needed hA (vdkInj_needed_of_diag h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_specPos_of_sr_of_diag

/-- **Endpoint**: (A) for `k ≥ 2` (Bass–Vaserstein; `k = 0, 1` are proved) and the diagonal
residual give `VdKRowExtensionStatement`. -/
theorem vdkInj_vdkRowExt_of_high_diag (hA : vdkStab_PolyStableRangeHighStatement)
    (h : vdkInj_DiagStatement) : VdKRowExtensionStatement :=
  vdkInj_vdkRowExt_of_high_needed hA (vdkInj_needed_of_diag h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInj_vdkRowExt_of_high_diag

end GroupApproximation.BooneHigman.Metabelian.ElemFP
