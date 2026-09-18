import Mathlib.Algebra.MvPolynomial.Nilpotent
import GroupApproximation.BooneHigman.Metabelian.VdKDiagEndpoint
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.Meta.AxiomGuard

/-!
# The diagonal statement is equivalent to the row-core residual

Lane `bh-met-90v`.  Target: `vdkInj_DiagStatement`, by a route that uses the specialization
hypothesis on `u` (every ring map `ψ : R_k → R_j`, `j < k`, kills `u`), leaving a residual
strictly weaker than lane `bh-met-90p`'s `vdkDiag_RowCoreStatement`.

## LOUD: no such residual exists

The specialization hypothesis gives **no logical leverage**.  Here `R_k = F_p[s_1, …, s_k]`.

* `vdkRowCoreX_two_le`: `sr(R_k) ≤ r` with `k > 0` forces `r ≥ 2`.  The row
  `(1 + s_1, s_1²)` is unimodular, because `(1 + s_1)(1 - s_1) + s_1² = 1`.  But
  `1 + s_1 + b s_1²` is never a unit, because its `s_1`-coefficient is `1`, which is not
  nilpotent.
* `vdkRowCoreX_stableRangeLE_of_retract`: `sr ≤ r` passes to ring retracts, so `sr(R_j) ≤ r`
  for `j ≤ k` (`rename`/`killCompl`).
* `vdkRowCoreX_injective_of_diag`: by strong induction on `j` at the **fixed rank `r + 3`**,
  `vdkInj_DiagStatement` gives injectivity of `K2Stab (r + 3)` on all of `K₂(r + 3, R_j)`
  whenever `sr(R_j) ≤ r`.
  - Base case: `j = 0` is the field case `vdkRowExt_fieldStab`, using `r + 3 ≥ 5`.
  - Step: for `j > 0`, naturality gives `K2Stab (ψ u) = ψ (K2Stab u) = 1`.  The induction
    hypothesis at `i < j`, using `sr(R_i) ≤ r` by retract, gives `ψ u = 1`.  So the
    specialization hypothesis holds automatically.
* `vdkRowCoreX_diag_iff_injective`: hence the diagonal statement is equivalent to plain
  injective stability of `K2Stab (r + 3)` over `R_k` (`k > 0`, `sr ≤ r`), with no hypothesis
  on `u`.
* `vdkRowCoreX_rowCore_of_diag`, `vdkRowCoreX_diag_iff_rowCore`: through the coset row data
  (`vdkRowDataOfInjective`), the diagonal statement is **equivalent** to
  `vdkDiag_RowCoreStatement`.

So every Statement `S` with `vdkDiag_RowCoreStatement → S → vdkInj_DiagStatement` is
equivalent to both.  A residual strictly weaker than `vdkDiag_RowCoreStatement` that still
implies the target cannot exist.  Instancewise, at a fixed `k`, `Diag_k` is weaker than
`RowCore_k`.  But `Diag` at every `j < k` already recovers the instance hypothesis, so any gain
is lost once all `j < k` are needed.  This is the same collapse as
`K2InjStabSpecializationStatement` (lane `bh-met-80`).

## Why routes (a) and (b) were not taken

* (a) Build a `vdkDiag_RowCore` on an explicit `X` only in the specialized situation.  A
  `RowCore` does not depend on `u`, so no specialization hypothesis on `u` can enter its
  construction.
  - Taking `X` to be a general `St`-set whose stabilizers meet `P̃` trivially is instancewise
    equivalent to the diagonal statement, through the coset construction.
  - The explicit choice `X = St / ι(K₂(n, R_{k-1}))` gives a `ker ev₀`-type statement, which
    is instancewise stronger.
* (b) A direct proof of the diagonal statement is, by the equivalence above, a proof of
  van der Kallen's injective stability at rank `r + 3` over `R_k`.  That is not available
  without literature inputs.

## Remaining gap

`vdkInj_DiagStatement` itself, or equivalently `vdkDiag_RowCoreStatement`.  It is true, because
it follows from `vdkStab_InjStabStatement` (`vdkDiag_rowCore_of_injStab`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- **Stable range passes to retracts**: if `g ∘ f = id` and `sr(B) ≤ r`, then `sr(A) ≤ r`. -/
theorem vdkRowCoreX_stableRangeLE_of_retract {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (g : B →+* A) (hgf : g.comp f = RingHom.id A) {r : ℕ}
    (h : vdkStab_StableRangeLE B r) : vdkStab_StableRangeLE A r := by
  have hgf' : ∀ x, g (f x) = x := fun x ↦ RingHom.congr_fun hgf x
  intro n hn v hv
  obtain ⟨b, hb⟩ := h n hn (fun i ↦ f (v i)) (vdkStab_isUnimodular_map f (fun _ ↦ rfl) hv)
  refine ⟨fun i ↦ g (b i), vdkStab_isUnimodular_map g (fun i ↦ ?_) hb⟩
  simp only [vdkStab_reduceRow_apply, map_add, map_mul, hgf']

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_stableRangeLE_of_retract

/-- The row `(a, c)` of length two. -/
def vdkRowCoreX_row {R : Type*} [CommRing R] (a c : R) : Fin (1 + 1) → R :=
  Fin.snoc (α := fun _ ↦ R) (fun _ ↦ a) c

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_row

theorem vdkRowCoreX_row_castSucc {R : Type*} [CommRing R] (a c : R) (i : Fin 1) :
    vdkRowCoreX_row a c i.castSucc = a :=
  Fin.snoc_castSucc (α := fun _ ↦ R) c (fun _ ↦ a) i

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_row_castSucc

theorem vdkRowCoreX_row_last {R : Type*} [CommRing R] (a c : R) :
    vdkRowCoreX_row a c (Fin.last 1) = c :=
  Fin.snoc_last (α := fun _ ↦ R) c (fun _ ↦ a)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoreX_row_last
