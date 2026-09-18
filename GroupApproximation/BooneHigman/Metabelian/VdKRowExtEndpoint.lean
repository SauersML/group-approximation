import GroupApproximation.BooneHigman.Metabelian.ElemFPK2InjStabSpecial
import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.Meta.AxiomGuard

/-!
# The row-extension gap: field case removed, reduced to positive-variable specialized stability

Lane `bh-met-90b`.  Target: `VdKRowExtensionStatement` (module `ElemFPK2VdKEndpoint`).

## Route

`VdKRowExtensionStatement` ⇐ `VdKRowParInjectiveStatement` (lane `bh-met-62`) ⇐
`K2InjStabSpecializationStatement` (lane `bh-met-80`).  The `k = 0` instances of the latter are
injective stability of `K₂(N, F_p)`, which is now proved outright (`vdkRowExt_fieldStab`,
module `VdKRowExtField`, from the big Bruhat cell).  What remains is:

* `VdKRowExtSpecPosStatement`: for `p` prime, `k > 0`, `N ≥ k + 4`, an element
  `u ∈ K₂(N, F_p[s_1, …, s_k])` with `K2Stab N u = 1` is trivial, provided `K2Map ψ u = 1` for
  every `j < k` and every ring map `ψ : F_p[s_1, …, s_k] →+* F_p[s_1, …, s_j]`.

## What is proved

* `vdkRowExt_specialization_of_specPos`: `VdKRowExtSpecPosStatement → K2InjStabSpecialization`.
* `vdkRowExt_of_specPos`: **endpoint**, `VdKRowExtSpecPosStatement → VdKRowExtensionStatement`.
* `vdkRowExt_specPos_of_nilStabilityPos`: the `ker ev₀` gap `PolyK2NilStabilityPosStatement`
  implies the residual (`ψ = C ∘ ev₀` is one of the specializations).
* `vdkRowExt_of_polyK2StabRangeDiag`: `PolyK2StabRangeDiagStatement → VdKRowExtensionStatement`
  **unconditionally**.  The earlier circularity remark of lane `bh-met-70c` needed the field
  input `FieldK2VanishingStatement`; that input is now a theorem.
* `vdkRowExt_specPos_of_vdkRowExtension`, `vdkRowExt_iff_specPos`,
  `vdkRowExt_iff_polyK2StabRangeDiag`: the converses.

## LOUD: strength of the residual

`VdKRowExtSpecPosStatement` is **instancewise weaker** than `K2InjStabSpecializationStatement`
(it drops every `k = 0` instance, and `5 ≤ N` is automatic from `k > 0`), and instancewise weaker
than `PolyK2NilStabilityPosStatement` (its hypothesis on `u` is stronger: all specializations to
fewer variables, not only `ev₀`).  But it is **logically equivalent** to
`VdKRowExtensionStatement`: both directions are proved here (`vdkRowExt_iff_specPos`).  So is
`PolyK2StabRangeDiagStatement` (`vdkRowExt_iff_polyK2StabRangeDiag`).  This is unavoidable
without proving van der Kallen's theorem: every cut of the gap that is still sufficient is
injective `K₂` stability for `F_p[s_1, …, s_k]` at rank `k + 4` in disguise.  The proof content
removed here is the field case (`k = 0`) and the rank side condition.

## Truth check

`VdKRowExtensionStatement` is true (van der Kallen's injective stability `n ≥ sr + 2` with Bass's
`sr(F_p[s_1, …, s_k]) ≤ k + 1`; rank `k + 4` has one to spare).  The residual follows from it
(`vdkRowExt_specPos_of_vdkRowExtension`), so it is true.  No `K₂` computation is feasible; the
stable-range ingredient was sanity-checked for `F_2[s]` (all 3073 unimodular rows of length 3
with entries of degree ≤ 3 reduce to unimodular rows of length 2, i.e. `sr ≤ 2`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The isolated residual.**  Injective stability of `K₂(N, F_p[s_1, …, s_k])` for `k > 0`,
`N ≥ k + 4`, on elements that die under every ring map to a polynomial ring in fewer variables.
LOUD: logically equivalent to `VdKRowExtensionStatement` (`vdkRowExt_iff_specPos`); instancewise
weaker than `K2InjStabSpecializationStatement` (no field case) and than
`PolyK2NilStabilityPosStatement` (stronger hypothesis on `u`). -/
def VdKRowExtSpecPosStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, 0 < k → k + 4 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      (∀ j : ℕ, j < k →
        ∀ ψ : MvPolynomial (Fin k) (ZMod p) →+* MvPolynomial (Fin j) (ZMod p),
          K2Map ψ u = 1) →
      K2Stab N (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowExtSpecPosStatement

/-- The residual, with the field case proved outright, gives lane `bh-met-80`'s
`K2InjStabSpecializationStatement`. -/
theorem vdkRowExt_specialization_of_specPos (h : VdKRowExtSpecPosStatement) :
    K2InjStabSpecializationStatement := by
  intro p hp k N hkN h5N u hψ hu
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact vdkRowExt_fieldStab p hp N h5N
      (hu.trans (map_one (K2Stab N (MvPolynomial (Fin 0) (ZMod p)))).symm)
  · exact h p hp k N hk hkN u hψ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_specialization_of_specPos

/-- **Endpoint**: the residual gives `VdKRowExtensionStatement`. -/
theorem vdkRowExt_of_specPos (h : VdKRowExtSpecPosStatement) : VdKRowExtensionStatement :=
  vdkRowExtension_of_vdkRowParInjective
    (k2InjStab_vdkRowParInjective_of_specialization (vdkRowExt_specialization_of_specPos h))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_of_specPos

/-- The `ker ev₀` gap gives the residual: `C ∘ ev₀` is a specialization to no variables. -/
theorem vdkRowExt_specPos_of_nilStabilityPos (h : PolyK2NilStabilityPosStatement) :
    VdKRowExtSpecPosStatement :=
  fun p hp k N hk hkN u hψ hu ↦
    h p hp k N hk hkN (by omega) u (k2InjStab_constantCoeff_eq_one hk u hψ) hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_specPos_of_nilStabilityPos

/-- **Unconditional**: the diagonal stable-range statement gives `VdKRowExtensionStatement`; the
field input of `vdkRowParInjective_of_stabRangeDiag_of_field` is now a theorem. -/
theorem vdkRowExt_of_polyK2StabRangeDiag (h : PolyK2StabRangeDiagStatement) :
    VdKRowExtensionStatement :=
  vdkRowExtension_of_vdkRowParInjective
    (vdkRowParInjective_of_stabRangeDiag_of_field h vdkRowExt_fieldK2Vanishing)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_of_polyK2StabRangeDiag

/-- LOUD, the converse: `VdKRowExtensionStatement` gives the residual back. -/
theorem vdkRowExt_specPos_of_vdkRowExtension (h : VdKRowExtensionStatement) :
    VdKRowExtSpecPosStatement := by
  have hs : K2InjStabSpecializationStatement :=
    k2InjStab_specialization_of_target
      (vdkRowParInjK2Stab_of_vdkRowParInjective
        (vdkRowParInjective_of_stabRangeDiag_of_field
          (polyK2StabRangeDiag_of_vdkRowExtension h) vdkRowExt_fieldK2Vanishing))
  intro p hp k N hk hkN u hψ hu
  exact hs p hp k N hkN (by omega) u hψ hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_specPos_of_vdkRowExtension

/-- LOUD: the residual is logically equivalent to the target. -/
theorem vdkRowExt_iff_specPos : VdKRowExtensionStatement ↔ VdKRowExtSpecPosStatement :=
  ⟨vdkRowExt_specPos_of_vdkRowExtension, vdkRowExt_of_specPos⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_iff_specPos

/-- The target is equivalent, unconditionally, to the diagonal stable-range gap that the chain
consumes. -/
theorem vdkRowExt_iff_polyK2StabRangeDiag :
    VdKRowExtensionStatement ↔ PolyK2StabRangeDiagStatement :=
  ⟨polyK2StabRangeDiag_of_vdkRowExtension, vdkRowExt_of_polyK2StabRangeDiag⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowExt_iff_polyK2StabRangeDiag

end GroupApproximation.BooneHigman.Metabelian.ElemFP
