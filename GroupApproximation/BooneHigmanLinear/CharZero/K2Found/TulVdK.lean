import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.TulXInst
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKUnique
import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKNatural
import GroupApproximation.Meta.AxiomGuard

/-!
# Locality of van der Kallen's constructed elements (bridge to k2-vdk's `VdK.elements`)

k2-vdk constructs `VdK.elements I A h4 : VdK.Elements I A` (vdK 3.7–3.22, for
`4 ≤ |I|`). For `w` with two zeros it proves `elt (v, w) = xvw v w r`
(`VdK.elements_elt_eq_xvw`), where
`xvw v w r = x_r(v_r w) ⁅x(v)_r, x_r(w)⁆` is vdK's elementary element 3.10.
* `ex_elements_eq_xvw`: `TulElem.ex` for these elements is `xvw`.
* `isLocal_elements`: the elements satisfy `TulElem.IsLocal`.
* `tulX_of_vdk`: `PaninAffine.TulX r` for `r ≥ 5` from k2-vdk's elements and their naturality.
* `eltNatural_elements`: that naturality, from `VdK.elements_natural`.
* **`tulX r h5 : PaninAffine.TulX r`**, with no hypotheses beyond `r ≥ 5`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace TulElem

open Matrix
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Found.VdK (U Elements IsUnimodular)

variable {I A : Type*} [Fintype I] [DecidableEq I] [CommRing A]

theorem colProd_add_single (r : I) (v : I → A) (c : A) :
    VdK.colProd r (v + c • Pi.single r 1) = VdK.colProd r v := by
  rw [VdK.colProd_add, ← Pi.single_smul', smul_eq_mul, mul_one, VdK.colProd_single_self, mul_one]

/-- For k2-vdk's elements, `X_r(v, w) = xvw v w r` when `w` has two zeros `r ≠ s`. -/
theorem ex_elements_eq_xvw (h4 : 4 ≤ Fintype.card I) {r s : I} (hrs : r ≠ s) {v w : I → A}
    (hr : w r = 0) (hs : w s = 0) (hw : w ⬝ᵥ v = 0) :
    ex (VdK.elements I A h4) r v w = VdK.xvw v w r := by
  have hq1 : (Pi.single r (1 : A), (v r - 1) • w) ∈ U I A :=
    memU (isUnimodular_single r) (smul_dot _ (dot_single hr))
  have hq2 : (v + (1 - v r) • Pi.single r (1 : A), w) ∈ U I A :=
    memU (isUnimodular_of_apply (tl_apply v r)) (dot_tl hr hw _)
  have hsum : (v r - 1) • w + w = v r • w := by module
  rw [ex, E_of_mem (VdK.elements I A h4) hq1, E_of_mem (VdK.elements I A h4) hq2,
    VdK.elements_elt_eq_xvw h4 hq1 hrs (by rw [Pi.smul_apply, hr, smul_zero])
      (by rw [Pi.smul_apply, hs, smul_zero]),
    VdK.elements_elt_eq_xvw h4 hq2 hrs hr hs, VdK.xvw_single_self, one_smul, VdK.xvw, VdK.xvw,
    tl_apply, one_smul, colProd_add_single, ← mul_assoc, ← VdK.rowProd_add, hsum]

#audit_axioms ex_elements_eq_xvw

/-- **k2-vdk's elements are local**: `X(v, w) = X_r(v, w)` when `w` has two zeros. -/
theorem isLocal_elements (h4 : 4 ≤ Fintype.card I) : IsLocal (VdK.elements I A h4) := by
  intro v w r s hrs hr hs hw hv
  rw [E_of_mem (VdK.elements I A h4) (memU hv hw),
    VdK.elements_elt_eq_xvw h4 (memU hv hw) hrs hr hs,
    ex_elements_eq_xvw h4 hrs hr hs hw]

#audit_axioms isLocal_elements

/-- **`PaninAffine.TulX r` from k2-vdk's elements**, for `r ≥ 5`, given their naturality. -/
noncomputable def tulX_of_vdk {r : ℕ} (h5 : 5 ≤ r)
    (hnat : ∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C),
      EltNatural (VdK.elements (Fin r) B (by rw [Fintype.card_fin]; omega))
        (VdK.elements (Fin r) C (by rw [Fintype.card_fin]; omega)) f) :
    PaninAffine.TulX r :=
  haveI : ∀ (B : Type) [CommRing B],
      Fact (IsLocal (VdK.elements (Fin r) B (by rw [Fintype.card_fin]; omega))) :=
    fun _ _ => ⟨isLocal_elements _⟩
  tulX_of_elements (fun B _ => VdK.elements (Fin r) B (by rw [Fintype.card_fin]; omega)) hnat h5

/-- **k2-vdk's elements are natural** (`VdK.elements_natural`), in the form `EltNatural`. -/
theorem eltNatural_elements (h4 : 4 ≤ Fintype.card I) {B C : Type*} [CommRing B] [CommRing C]
    (f : B →+* C) : EltNatural (VdK.elements I B h4) (VdK.elements I C h4) f := by
  intro v w h
  obtain ⟨⟨k, hk⟩, hw⟩ := VdK.mem_U.1 h
  have h' : (f ∘ v, f ∘ w) ∈ U I C :=
    memU ⟨f ∘ k, by rw [← RingHom.map_dotProduct, hk, map_one]⟩
      (by rw [← RingHom.map_dotProduct, hw, map_zero])
  rw [E_of_mem (VdK.elements I B h4) h, E_of_mem (VdK.elements I C h4) h']
  exact VdK.elements_natural h4 f h h'

#audit_axioms eltNatural_elements

/-- **Tulenbaev's elements `X_{v,w}(t)` with T 1.1–1.3, unconditionally** (`r ≥ 5`): the input
`PaninAffine.TulX r` of F.4, built on k2-vdk's `VdK.elements`. -/
noncomputable def tulX (r : ℕ) (h5 : 5 ≤ r) : PaninAffine.TulX r :=
  tulX_of_vdk h5 fun _ _ _ _ f => eltNatural_elements _ f

end TulElem
end K2Found
end BooneHigmanLinear
end GroupApproximation
