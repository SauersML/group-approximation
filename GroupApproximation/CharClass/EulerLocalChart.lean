import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Charts around an isolated zero: homeomorphisms of punctured pairs

Step C's local computation (`notes/LIX_FULL_PROGRAM_2026-09-05.md` §1.3, item 2 of
lane `cc-thom`) reads: the section `s` has a single zero `z`, near which it is a
homeomorphism onto a neighbourhood of `0` in the fibre `ℂ^r`; so `s^* u` restricted to
a chart pair `(D, D ∖ z)` is the generator of `H^{2r}(D, D ∖ z; F₂) ≅ F₂`.  The
cohomological half of that is excision and homeomorphism invariance of pairs
(`cc-relative`, needs (B3)/(B4)); the *topological* half is that a homeomorphism
carrying `z` to `0` is a homeomorphism **of pairs**

```text
(D, D ∖ z) ≅ (V, V ∖ 0),
```

which is what this file provides.  There is deliberately no degree computation
anywhere: the generator is transported, never recomputed.

## Main definitions

* `homeomorphCompl` — a homeomorphism `X ≃ₜ Y` restricts to
  `X ∖ a ≃ₜ Y ∖ e a`.
* `compl_singleton_subtype` — inside a subspace `D ∋ z`, the complement of the point
  `⟨z, hz⟩` is the preimage of `X ∖ z`; this is the bookkeeping that matches the
  excision statement `H^n(X, X ∖ z) ≅ H^n(D, D ∖ z)`.
* `chartPairHomeo` — the homeomorphism of pairs induced by a chart taking the zero to
  the origin.
-/

namespace GroupApproximation.CharClass

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A homeomorphism restricts to the punctured spaces.**  If `e : X ≃ₜ Y` then
`X ∖ {a} ≃ₜ Y ∖ {e a}`. -/
def homeomorphCompl (e : X ≃ₜ Y) (a : X) :
    ↥({a}ᶜ : Set X) ≃ₜ ↥({e a}ᶜ : Set Y) where
  toFun x := ⟨e x, fun h => x.2 (e.injective h)⟩
  invFun y := ⟨e.symm y, fun h =>
    y.2 ((e.apply_symm_apply (y : Y)).symm.trans (congrArg (e : X → Y) h))⟩
  left_inv x := Subtype.ext (e.symm_apply_apply _)
  right_inv y := Subtype.ext (e.apply_symm_apply _)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
theorem homeomorphCompl_apply_coe (e : X ≃ₜ Y) (a : X) (x : ↥({a}ᶜ : Set X)) :
    ((homeomorphCompl e a x : ↥({e a}ᶜ : Set Y)) : Y) = e x := rfl

omit [TopologicalSpace X] in
/-- Inside a subspace `D` containing `z`, the complement of the point `⟨z, hz⟩` is the
preimage of the complement of `z`.  This is what lines the chart pair `(D, D ∖ z)` up
with the excision statement of `cc-relative`. -/
theorem compl_singleton_subtype (D : Set X) (z : X) (hz : z ∈ D) :
    ({(⟨z, hz⟩ : ↥D)}ᶜ : Set ↥D) = (Subtype.val : ↥D → X) ⁻¹' ({z}ᶜ : Set X) := by
  ext x
  simp [Subtype.ext_iff]

/-- **The chart pair homeomorphism.**  A chart `e : D ≃ₜ V` around the single zero `z`
of the section, taking `z` to the origin `o` of the local model, is a homeomorphism of
pairs `(D, D ∖ z) ≅ (V, V ∖ o)`. -/
def chartPairHomeo {D : Set X} {V : Set Y} (e : ↥D ≃ₜ ↥V) {z : X} (hz : z ∈ D)
    {o : Y} (ho : o ∈ V) (hzo : (e ⟨z, hz⟩ : ↥V) = ⟨o, ho⟩) :
    ↥((Subtype.val : ↥D → X) ⁻¹' ({z}ᶜ : Set X))
      ≃ₜ ↥((Subtype.val : ↥V → Y) ⁻¹' ({o}ᶜ : Set Y)) :=
  (Homeomorph.setCongr (compl_singleton_subtype D z hz).symm).trans
    ((homeomorphCompl e ⟨z, hz⟩).trans
      (Homeomorph.setCongr (by rw [hzo, compl_singleton_subtype V o ho])))

end GroupApproximation.CharClass
