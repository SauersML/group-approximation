import GroupApproximation.BooneHigman.Metabelian.ElemFPK2Homotopy
import GroupApproximation.Meta.AxiomGuard

/-!
# Injective stability for `K₂(N, F_p[s_1..s_k])`: reduction to the nil part, `k ≥ 1`

Lane `bh-met-14`.  `PolyK2InjectiveStabilityStatement` (module `ElemFPK2Split`) asks that
`K2Stab N R_k` be injective for `N ≥ k + 4`, `N ≥ 5`, where `R_k = F_p[s_1..s_k]`.  This module
isolates the unclosed piece.

* `PolyK2NilStabilityPosStatement`: for `k ≥ 1`, an element `u ∈ K₂(N, R_k)` with `ev₀ u = 1` and
  `K2Stab N R_k u = 1` is trivial.  **This is the isolated gap.**  It is strictly weaker than
  `PolyK2InjectiveStabilityStatement`: it is the injectivity statement restricted to `k ≥ 1`
  and to the kernel of `ev₀`.  Truth: it is the special case of van der Kallen's injective
  stability for `K₂` (stable rank of `R_k` at most `k + 1`, injectivity for `N ≥ k + 3`).
* `polyK2InjectiveStability_of_nilPos`: the gap and the field case give injective stability.
  For `u` in the kernel of `K2Stab`, `ev₀ u ∈ K₂(N, F_p) = ⊥`, so `ev₀ u = 1` automatically.  When
  `k = 0`, `ev₀` is injective (`eq_one_of_K2Map_constantCoeff_eq_one`).
* `polynomialFpK2Vanishing_of_nilPos`: the combined endpoint.  The target
  `PolynomialFpK2VanishingStatement` follows from the two nil gaps and the field case.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **The isolated stability gap**: injective stability on the kernel of `ev₀`, for `k ≥ 1`. -/
def PolyK2NilStabilityPosStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k N : ℕ, 0 < k → k + 4 ≤ N → 5 ≤ N →
    ∀ u : K2n N (MvPolynomial (Fin k) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) u = 1 →
        K2Stab N (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2NilStabilityPosStatement

/-- The stability gap and the field case give injective stability. -/
theorem polyK2InjectiveStability_of_nilPos (h : PolyK2NilStabilityPosStatement)
    (hfield : FieldK2VanishingStatement) : PolyK2InjectiveStabilityStatement := by
  intro p hp k N hkN h5N
  refine (injective_iff_map_eq_one _).mpr fun u hu ↦ ?_
  have hcc :
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) u = 1 :=
    eq_one_of_K2_eq_bot (hfield p hp N h5N) _
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact eq_one_of_K2Map_constantCoeff_eq_one hcc
  · exact h p hp k N hk hkN h5N u hcc hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2InjectiveStability_of_nilPos

/-- **Combined endpoint**: the two nil gaps (`k ≥ 1`) and the field case give
`K₂(N, F_p[s_1..s_k]) = 0` for `N ≥ k + 4`, `N ≥ 5`. -/
theorem polynomialFpK2Vanishing_of_nilPos (hstab : PolyK2NilStabilityPosStatement)
    (hnil : PolyK2NilPosStatement) (hfield : FieldK2VanishingStatement) :
    PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_split (polyK2InjectiveStability_of_nilPos hstab hfield)
    (polyK2Homotopy_of_nil (polyK2Nil_of_pos hnil)) hfield

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_nilPos

end GroupApproximation.BooneHigman.Metabelian.ElemFP
