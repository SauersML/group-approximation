import Mathlib.Algebra.MvPolynomial.Rename
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2Stability
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# Injective stability for `K₂(N, F_p[s_1..s_k])` on the kernel of `ev₀`: reduction to `N = k + 4`

Lane `bh-met-29`.  Lane `bh-met-14` (module `ElemFPK2Stability`) isolated
`PolyK2NilStabilityPosStatement`: for `p` prime, `k ≥ 1`, `N ≥ k + 4`, `N ≥ 5`, an element
`u ∈ K₂(N, R_k)`, `R_k = F_p[s_1..s_k]`, with `ev₀ u = 1` and `K2Stab N R_k u = 1` is trivial.
This module removes the rank parameter `N`: it suffices to treat the diagonal `N = k + 4`.

* `eq_one_of_K2Stab_retract`: for arbitrary rings.  Let `f : R → S` have a left inverse `g`, and
  let `cc_S ∘ f = cc_R`.  If the statement "`cc_S v = 1` and `K2Stab n S v = 1` imply `v = 1`"
  holds over `S`, it holds over `R`.  Transport `u` to `f u`: coefficient maps commute with
  `cc` (by `cc_S ∘ f = cc_R`) and with stabilization (`K2IndexMap_K2Map`), so `f u = 1`, and then
  `u = g (f u) = 1` (`K2Map_K2Map_of_comp_eq_id`).
* `PolyK2StabRangeDiagStatement`: the diagonal case `N = k + 4`, `k ≥ 1`.
  **This is the isolated gap.**
* `polyK2NilStabilityPos_of_diag`: the diagonal gives the full statement.  Given `N ≥ k + 4`, put
  `k' = N - 4 ≥ k`.  The renaming `MvPolynomial.rename (Fin.castLE _) : R_k → R_{k'}` has the left
  inverse `MvPolynomial.killCompl _` (the extra variables go to `0`) and preserves the constant
  coefficient (`MvPolynomial.constantCoeff_rename`).  So the diagonal statement at `k'` transports
  to `R_k` at rank `N = k' + 4`.  The hypothesis `N ≥ 5` is then automatic (`k' ≥ k ≥ 1`).
* `polynomialFpK2Vanishing_of_stabRangeDiag`: the combined endpoint of the `K₂` vanishing chain
  with the diagonal gap in place of `PolyK2NilStabilityPosStatement`.

Why the gap is strictly smaller.  `PolyK2StabRangeDiagStatement` is the special case `N = k + 4` of
`PolyK2NilStabilityPosStatement` (so it is not logically stronger).  The passage to all ranks
`N ≥ k + 4`, i.e. the whole rank parameter, is proved here by the retraction argument.

Truth of the gap.  `R_k` is noetherian of Krull dimension `k`, so by Bass's theorem its stable
rank is `sr(R_k) ≤ k + 1`.  Injective stability for `K₂` (van der Kallen 1977: `K₂(n, R) →
K₂(n+1, R)` injective for `n ≥ sr(R) + 2`; already Dennis's older bound `n ≥ d + 3`,
`d = dim Max(R)`) applies at `n = k + 4 ≥ sr(R_k) + 3`, with one step of margin.  The restriction
to `ker ev₀` only weakens it.  As a sanity check at the smallest case `k = 1`, `N = 5`: `F_p[s]`
is a principal ideal domain, `sr ≤ 2`, and van der Kallen's bound asks only for `n ≥ 4`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic

/-- **Transport of injective stability along a retract**, for arbitrary rings.  If `f : R →+* S`
has a left inverse and is compatible with augmentations `cc_R`, `cc_S`, then stability on the
augmentation kernel over `S` gives it over `R`, at the same rank. -/
theorem eq_one_of_K2Stab_retract {R S Z : Type*} [Ring R] [Ring S] [Ring Z] {n : ℕ}
    (f : R →+* S) (g : S →+* R) (hgf : g.comp f = RingHom.id R)
    (ccR : R →+* Z) (ccS : S →+* Z) (hcc : ccS.comp f = ccR)
    (h : ∀ v : K2n n S, K2Map ccS v = 1 → K2Stab n S v = 1 → v = 1)
    (u : K2n n R) (hu0 : K2Map ccR u = 1) (hu : K2Stab n R u = 1) : u = 1 := by
  have hv0 : K2Map ccS (K2Map f u) = 1 := by
    rw [K2Map_K2Map, hcc, hu0]
  have hv : K2Stab n S (K2Map f u) = 1 :=
    (K2IndexMap_K2Map (Fin.castSuccEmb : Fin n ↪ Fin (n + 1)) f u).trans
      ((DFunLike.congr_arg (K2Map (I := Fin (n + 1)) f) hu).trans
        (map_one (K2Map (I := Fin (n + 1)) f)))
  calc u = K2Map g (K2Map f u) := (K2Map_K2Map_of_comp_eq_id g f hgf u).symm
    _ = K2Map g 1 := by rw [h _ hv0 hv]
    _ = 1 := map_one (K2Map (I := Fin n) g)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.eq_one_of_K2Stab_retract

/-- **The isolated gap**: injective stability on the kernel of `ev₀` at the diagonal rank
`N = k + 4`, for `k ≥ 1`. -/
def PolyK2StabRangeDiagStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ k : ℕ, 0 < k →
    ∀ u : K2n (k + 4) (MvPolynomial (Fin k) (ZMod p)),
      K2Map (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p) u = 1 →
        K2Stab (k + 4) (MvPolynomial (Fin k) (ZMod p)) u = 1 → u = 1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.PolyK2StabRangeDiagStatement

/-- The diagonal case gives injective stability on the kernel of `ev₀` at every rank
`N ≥ k + 4`, by adding `N - 4 - k` dummy variables. -/
theorem polyK2NilStabilityPos_of_diag (h : PolyK2StabRangeDiagStatement) :
    PolyK2NilStabilityPosStatement := by
  intro p hp k N hk hkN _ u hu0 hu
  obtain ⟨k', rfl⟩ : ∃ k' : ℕ, N = k' + 4 := ⟨N - 4, by omega⟩
  have hkk : k ≤ k' := by omega
  exact eq_one_of_K2Stab_retract
    (MvPolynomial.rename (R := ZMod p) (Fin.castLE hkk)).toRingHom
    (MvPolynomial.killCompl (R := ZMod p) (Fin.castLE_injective hkk)).toRingHom
    (RingHom.ext fun x ↦ MvPolynomial.killCompl_rename_app (Fin.castLE_injective hkk) x)
    (MvPolynomial.constantCoeff : MvPolynomial (Fin k) (ZMod p) →+* ZMod p)
    (MvPolynomial.constantCoeff : MvPolynomial (Fin k') (ZMod p) →+* ZMod p)
    (RingHom.ext fun x ↦ MvPolynomial.constantCoeff_rename (Fin.castLE hkk) x)
    (h p hp k' (hk.trans_le hkk)) u hu0 hu

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyK2NilStabilityPos_of_diag

/-- **Combined endpoint**: the diagonal stability gap, the nil gap and the field case give
`K₂(N, F_p[s_1..s_k]) = 0` for `N ≥ k + 4`, `N ≥ 5`. -/
theorem polynomialFpK2Vanishing_of_stabRangeDiag (hstab : PolyK2StabRangeDiagStatement)
    (hnil : PolyK2NilPosStatement) (hfield : FieldK2VanishingStatement) :
    PolynomialFpK2VanishingStatement :=
  polynomialFpK2Vanishing_of_nilPos (polyK2NilStabilityPos_of_diag hstab) hnil hfield

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFP.polynomialFpK2Vanishing_of_stabRangeDiag

end GroupApproximation.BooneHigman.Metabelian.ElemFP
