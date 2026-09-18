import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowParInjReadout
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2Stability
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2StabRange
import GroupApproximation.Meta.AxiomGuard

/-!
# `VdKRowParInjectiveStatement` is injective `K₂` stability at rank `k + 4`

Lane `bh-met-70c`.  Target: `VdKRowParInjectiveStatement` (module `ElemFPK2VdKRowEndpoint`).

* `vdkRowParInjective_iff_K2Stab_injective`: over any ring and at any rank, `vdkRowPar` is
  injective iff `K2Stab n R` is.  The forward direction is
  `K2Stab_eq_one_of_vdkRowPar_injective`.  The backward direction,
  `vdkRowParInjective_of_K2Stab_injective` (module `ElemFPK2VdKRowParInjReadout`), is new here.
  The earlier endpoint left it informal.
* `VdKRowParInjK2StabStatement`: `K2Stab (k + 4)` is injective over `F_p[s_1, …, s_k]`, `k > 0`.
* `vdkRowParInjective_of_K2Stab`: `VdKRowParInjK2StabStatement → VdKRowParInjectiveStatement`,
  and the converse `vdkRowParInjK2Stab_of_vdkRowParInjective`.
* `vdkRowParInjK2Stab_of_polyK2InjectiveStability`: the statement is the `N = k + 4` instance of
  the existing `PolyK2InjectiveStabilityStatement`.
* `vdkRowParInjective_of_stabRangeDiag_of_field`: `PolyK2StabRangeDiagStatement` and
  `FieldK2VanishingStatement` together give the target.

**LOUD: only equivalent, not weaker.**  The isolated `VdKRowParInjK2StabStatement` is
logically equivalent to the target.  Both directions are proved here.  It is not strictly weaker
in logic.  It is smaller in proof content: the whole group-side part is proved, and the matrix
readout, the cancellation and `ker stab ≤ K₂` are proved here.  What remains is the standard
injective stability statement for `K₂` of a polynomial ring.

**LOUD: the row-extension detour is circular modulo the field case.**
`polyK2StabRangeDiag_of_vdkRowParInjective` gives `VdKRowParInjective → PolyK2StabRangeDiag`.
`vdkRowParInjective_of_stabRangeDiag_of_field` gives `PolyK2StabRangeDiag ∧ FieldK2Vanishing →
VdKRowParInjective`.  So, given the field input, the `VdKRowParInjective` gap has exactly the
strength of the `PolyK2StabRangeDiag` gap that it was introduced to close.

Truth check (no Lean content).  The target is true.  `F_p[s_1, …, s_k]` has Krull dimension `k`,
so Bass gives `sr ≤ k + 1`.  Van der Kallen's injective stability gives `K₂(n) → K₂(n+1)`
injective for `n ≥ sr + 2`, which covers `n = k + 4` with one to spare.  Dennis's bound
`n ≥ dim + 3` also covers it.  An outright proof would need van der Kallen's theorem and Bass's
bound, neither of which is in the corpus.  So no retraction `St_{n+1} → St_n` and no normal
form can close it here without that theorem.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- Over any ring and at any rank, `vdkRowPar` is injective iff `K₂(n, R) → K₂(n+1, R)` is. -/
theorem vdkRowParInjective_iff_K2Stab_injective {R : Type*} [Ring R] {n : ℕ} :
    Function.Injective (vdkRowPar (n := n) (R := R)) ↔ Function.Injective (K2Stab n R) :=
  ⟨fun hinj => (injective_iff_map_eq_one (K2Stab n R)).mpr
      (K2Stab_eq_one_of_vdkRowPar_injective hinj),
    vdkRowParInjective_of_K2Stab_injective⟩

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInjective_iff_K2Stab_injective

/-- **The isolated gap**: injective `K₂` stability `K₂(k+4) → K₂(k+5)` over
`F_p[s_1, …, s_k]`, `k > 0`.  LOUD: logically equivalent to `VdKRowParInjectiveStatement`,
via `vdkRowParInjective_iff_K2Stab_injective`.  It is the `N = k + 4` case of
`PolyK2InjectiveStabilityStatement`.  It is true by van der Kallen and Bass (module docstring). -/
def VdKRowParInjK2StabStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 0 < k →
    Function.Injective (K2Stab (k + 4) (MvPolynomial (Fin k) (ZMod p)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowParInjK2StabStatement

/-- **Endpoint**: injective `K₂` stability at rank `k + 4` gives `VdKRowParInjectiveStatement`. -/
theorem vdkRowParInjective_of_K2Stab (h : VdKRowParInjK2StabStatement) :
    VdKRowParInjectiveStatement :=
  fun p hp k hk => vdkRowParInjective_of_K2Stab_injective (h p hp k hk)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInjective_of_K2Stab

/-- The converse: the isolated statement is no stronger than the target. -/
theorem vdkRowParInjK2Stab_of_vdkRowParInjective (h : VdKRowParInjectiveStatement) :
    VdKRowParInjK2StabStatement :=
  fun p hp k hk => vdkRowParInjective_iff_K2Stab_injective.mp (h p hp k hk)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInjK2Stab_of_vdkRowParInjective

/-- The isolated statement is the `N = k + 4` instance of `PolyK2InjectiveStabilityStatement`. -/
theorem vdkRowParInjK2Stab_of_polyK2InjectiveStability
    (h : PolyK2InjectiveStabilityStatement) : VdKRowParInjK2StabStatement :=
  fun p hp k hk => h p hp k (k + 4) le_rfl (by omega)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInjK2Stab_of_polyK2InjectiveStability

/-- Injective `K₂` stability for polynomial rings gives the target. -/
theorem vdkRowParInjective_of_polyK2InjectiveStability
    (h : PolyK2InjectiveStabilityStatement) : VdKRowParInjectiveStatement :=
  vdkRowParInjective_of_K2Stab (vdkRowParInjK2Stab_of_polyK2InjectiveStability h)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInjective_of_polyK2InjectiveStability

/-- **LOUD (circularity)**: the diagonal stable-range statement and the field case give the
target back.  Together with `polyK2StabRangeDiag_of_vdkRowParInjective`, this makes
`VdKRowParInjectiveStatement` and `PolyK2StabRangeDiagStatement` equivalent given
`FieldK2VanishingStatement`. -/
theorem vdkRowParInjective_of_stabRangeDiag_of_field (h : PolyK2StabRangeDiagStatement)
    (hfield : FieldK2VanishingStatement) : VdKRowParInjectiveStatement :=
  vdkRowParInjective_of_polyK2InjectiveStability
    (polyK2InjectiveStability_of_nilPos (polyK2NilStabilityPos_of_diag h) hfield)

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowParInjective_of_stabRangeDiag_of_field

end GroupApproximation.BooneHigman.Metabelian.ElemFP
