import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXa3
import GroupApproximation.Meta.AxiomGuard

/-!
# Tulenbaev's Lemma 1.3(c): `X_{v+cv',w}(a) = X_{v,w}(a) X_{v',w}(ca)`

M. S. Tulenbaev, *The Steinberg group of a polynomial ring*, Lemma 1.3(c). Let `w` lie in the
span of the rows orthogonal to both `v` and `v'` with two zeros (`TwoZero.twoZeroSet v v'`). By
T Lemma 1.2 (`TwoZero.det_smul_mem_span_twoZero`) this holds for `aⁿ w` when `(v, v')` is
unimodular over `A[1/a]`. Write `w = ∑ w_k` accordingly. Each factor splits by T 1.1(a) and (d):
`X(v + c v', t w_k) = X(v, t w_k) X(v', c t w_k)`. The two products are then separated by
T 1.1(e), which applies because each `w_k` kills both columns (`coe_prod_mul`).
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (Elements)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A] (hX : Elements I A)
  [Fact (IsLocal hX)]

/-- **Tulenbaev's Lemma 1.3(c)**: `X_{v+cv',w}(t) = X_{v,w}(t) X_{v',w}(ct)`, where
`t = u (v + c v')`, `u₁ v = t` and `u₂ v' = c t`. -/
theorem Xa_col_add (h4 : 4 ≤ Fintype.card I) {v v' w : I → A}
    (hw : w ∈ Submodule.span A (TwoZero.twoZeroSet v v')) (c : A) (u u₁ u₂ : I → A)
    (h1 : u₁ ⬝ᵥ v = u ⬝ᵥ (v + c • v')) (h2 : u₂ ⬝ᵥ v' = c * (u ⬝ᵥ (v + c • v'))) :
    Xa hX h4 (v + c • v') w u = Xa hX h4 v w u₁ * Xa hX h4 v' w u₂ := by
  obtain ⟨n, a, g, hg⟩ := Submodule.mem_span_set'.mp hw
  have hfv : ∀ k, (a k • (g k : I → A)) ⬝ᵥ v = 0 := fun k => smul_dot _ (g k).2.1
  have hfv' : ∀ k, (a k • (g k : I → A)) ⬝ᵥ v' = 0 := fun k => smul_dot _ (g k).2.2.1
  have hf2 : ∀ k, TwoZ (a k • (g k : I → A)) := fun k => TwoZ.smul (g k).2.2.2 (a k)
  have hfs : ∀ k, (a k • (g k : I → A)) ⬝ᵥ (v + c • v') = 0 := fun k => by
    rw [dotProduct_add, dotProduct_smul, hfv, hfv', smul_zero, add_zero]
  rw [← hg, Xa_eq_prod hX h4 (v + c • v') u _ _ hfs hf2, Xa_eq_prod hX h4 v u₁ _ _ hfv hf2,
    Xa_eq_prod hX h4 v' u₂ _ _ hfv' hf2]
  refine coe_prod_mul hX _ _ _ _ (fun k => ?_) (fun k l => ?_)
  · obtain ⟨r, s, hrs, hr, hs⟩ := hf2 k
    have hxr : ((u ⬝ᵥ (v + c • v')) • (a k • (g k : I → A))) r = 0 := by
      rw [Pi.smul_apply, hr, smul_zero]
    have hxs : ((u ⬝ᵥ (v + c • v')) • (a k • (g k : I → A))) s = 0 := by
      rw [Pi.smul_apply, hs, smul_zero]
    have hxr' : ((c * (u ⬝ᵥ (v + c • v'))) • (a k • (g k : I → A))) r = 0 := by
      rw [Pi.smul_apply, hr, smul_zero]
    rw [coe_txc, coe_txc, coe_txc, h1, h2, tx_eq hX hxr (smul_dot _ (hfs k)),
      ex_add_left hX hrs hxr hxs (smul_dot _ (hfv k)) (dot_smul_zero c (smul_dot _ (hfv' k))),
      ex_smul_left hX hrs hxr hxs (smul_dot _ (hfv' k)), smul_smul c (u ⬝ᵥ (v + c • v')),
      tx_eq hX (v := v) hxr (smul_dot _ (hfv k)), tx_eq hX (v := v') hxr' (smul_dot _ (hfv' k))]
  · rw [coe_txc, coe_txc]
    obtain ⟨r, -, -, hr, -⟩ := hf2 k
    exact tx_commute hX Fact.out ⟨r, by rw [Pi.smul_apply, hr, smul_zero]⟩ ((hf2 l).smul _)
      (smul_dot _ (hfv' k)) (smul_dot _ (hfv k)) (smul_dot _ (hfv' l)) (smul_dot _ (hfv l))

#audit_axioms Xa_col_add

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
