import GroupApproximation.BooneHigman.Metabelian.VdKRowExtField
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2OneVarTransport
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` versus the constants: the constant part, discharged

Lane `bh-met-90u`.  Target (field building block): for a field `F` and `N ≥ 5`, every element of
`K₂(N, F[X])` is `C w` for some `w ∈ K₂(N, F)`.  For `F = F_p` this means
`K₂(N, F_p[X]) = 0`, because `K₂(N, F_p) = 0` (`vdkRowExt_fieldK2Vanishing`).

This module does **not** prove the target.  It isolates the residual
`k2PolyField_ConstStatement F N`: every `g ∈ K₂(N, F[X])` lies in the image of the whole
Steinberg group `St(N, F)` under `C`.  It then discharges everything else outright:

* `k2PolyField_exists_K2_of_mem_range` (any commutative ring `A`, any index type): if
  `g ∈ K₂(I, A[X])` is `C y` with `y ∈ St(I, A)`, then `y ∈ K₂(I, A)`.  Apply the retraction
  `ev_{X=0}`: it sends `g` into `K₂(I, A)` and `C y` back to `y`.
* `k2PolyField_eq_one_of_mem_range`: over `F_p` and for `N ≥ 5`, such a `g` is trivial, by the
  first item and the big Bruhat cell (`K₂(N, F_p) = 0`).
* `k2PolyField_mem_image_of_const`: the residual gives the target in its `K₂` form.
* `k2PolyField_const_of_mem_image`: the converse.
* `k2PolyField_K2_eq_bot_of_const`: the residual over `F_p` gives `K₂(N, F_p[X]) = ⊥`.

**LOUD strength note.** `k2PolyField_ConstStatement F N` is **logically equivalent** to the
target for each fixed `F` and `N` (see the two items above that prove each direction).  Per
element it asks for less, since `ringMap C` has a larger domain than `K₂(N, F)`.  The only proof
content it removes is the `ev_0` retraction.  Over `F_p` it also removes `K₂(N, F_p) = 0` (the
Bruhat big cell), which is the part of `K₂(N, F_p[X]) = 0` that lives in degree `0`.
What remains is exactly the positive-degree part: every relation among elementary matrices over
`F[X]` is a consequence of relations over `F`.  That is the degree-reduction step in Milnor's
proof, which is not formalised here.

**Truth.** The residual is true for every field `F` and every `N ≥ 5`.  This follows from
`K₂(F[X]) = K₂(F)` for regular rings together with injective stability for `F[X]`, a Euclidean
domain.  It is recorded here only as a truth check and is not used as a hypothesis.  The
Statement is phrased for any commutative ring, but it is false for non-regular rings such as
`F[ε]/(ε²)`, so it should only be instantiated at fields.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic

section Retract

/-- **Degree `0`, ring-generic.** An element of `K₂(I, A[X])` that is the image `C y` of some
`y ∈ St(I, A)` is the image of an element of `K₂(I, A)`, namely `y` itself: `ev_{X=0}` sends
`C y` to `y` and carries `K₂` into `K₂`. -/
theorem k2PolyField_exists_K2_of_mem_range {A : Type*} [CommRing A] {I : Type*} [Fintype I]
    [DecidableEq I] {g : SteinbergGroup I (Polynomial A)} (hg : g ∈ K2 I (Polynomial A))
    (hr : g ∈ (ringMap (I := I) (Polynomial.C : A →+* Polynomial A)).range) :
    ∃ w : K2 I A, (K2Map (Polynomial.C : A →+* Polynomial A) w :
      SteinbergGroup I (Polynomial A)) = g := by
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hr
  have hy : ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A)
      (ringMap (Polynomial.C : A →+* Polynomial A) y) = y := by
    rw [ringMap_ringMap, evalRingHom_zero_comp_C, ringMap_id, MonoidHom.id_apply]
  have h := ringMap_mem_K2 (Polynomial.evalRingHom 0 : Polynomial A →+* A) hg
  rw [hy] at h
  exact ⟨⟨y, h⟩, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyField_exists_K2_of_mem_range

/-- **Degree `0` over `F_p`.** For `N ≥ 5`, an element of `K₂(N, F_p[X])` in the image of
`St(N, F_p)` under `C` is trivial.  Its preimage lies in `K₂(N, F_p) = 0` (big Bruhat cell). -/
theorem k2PolyField_eq_one_of_mem_range {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N)
    {g : St N (Polynomial (ZMod p))} (hg : g ∈ K2n N (Polynomial (ZMod p)))
    (hr : g ∈ (ringMap (I := Fin N) (Polynomial.C : ZMod p →+* Polynomial (ZMod p))).range) :
    g = 1 := by
  obtain ⟨w, hw⟩ := k2PolyField_exists_K2_of_mem_range hg hr
  have hw1 : w = 1 := eq_one_of_K2_eq_bot (vdkRowExt_fieldK2Vanishing p hp N hN) w
  rw [← hw, hw1, map_one, Subgroup.coe_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyField_eq_one_of_mem_range

end Retract

section Const

/-- **The residual (positive-degree part).** Every element of `K₂(N, F[X])` lies in the image of
the whole Steinberg group `St(N, F)` under the constant inclusion `C`.  Intended for fields `F`
and `N ≥ 5`, where it is true.  It is false for non-regular rings.  See the module docstring for
the LOUD note that this is logically equivalent to the target. -/
def k2PolyField_ConstStatement (F : Type*) [CommRing F] (N : ℕ) : Prop :=
  ∀ g : St N (Polynomial F), g ∈ K2n N (Polynomial F) →
    g ∈ (ringMap (I := Fin N) (Polynomial.C : F →+* Polynomial F)).range

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyField_ConstStatement

/-- The residual gives the target: every element of `K₂(N, F[X])` is `C w` with
`w ∈ K₂(N, F)`. -/
theorem k2PolyField_mem_image_of_const {F : Type*} [CommRing F] {N : ℕ}
    (h : k2PolyField_ConstStatement F N) (g : K2n N (Polynomial F)) :
    ∃ w : K2n N F, K2Map (Polynomial.C : F →+* Polynomial F) w = g := by
  obtain ⟨w, hw⟩ := k2PolyField_exists_K2_of_mem_range g.2 (h g g.2)
  exact ⟨w, Subtype.ext hw⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyField_mem_image_of_const

/-- The converse (LOUD: the residual is equivalent to the target). -/
theorem k2PolyField_const_of_mem_image {F : Type*} [CommRing F] {N : ℕ}
    (h : ∀ g : K2n N (Polynomial F),
      ∃ w : K2n N F, K2Map (Polynomial.C : F →+* Polynomial F) w = g) :
    k2PolyField_ConstStatement F N := by
  intro g hg
  obtain ⟨w, hw⟩ := h ⟨g, hg⟩
  exact MonoidHom.mem_range.mpr ⟨(w : St N F), congrArg Subtype.val hw⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyField_const_of_mem_image

/-- **Over `F_p`**: the residual gives `K₂(N, F_p[X]) = 0` for `N ≥ 5`. -/
theorem k2PolyField_K2_eq_bot_of_const {p : ℕ} (hp : p.Prime) {N : ℕ} (hN : 5 ≤ N)
    (h : k2PolyField_ConstStatement (ZMod p) N) : K2n N (Polynomial (ZMod p)) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦
    k2PolyField_eq_one_of_mem_range hp hN hg (h g hg)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyField_K2_eq_bot_of_const

/-- **Over `F_p`, any one-variable presentation**: if `σ` has exactly one element, then the
residual gives `K₂(N, F_p[σ]) = 0` for `N ≥ 5`.  The proof transports along
`MvPolynomial.uniqueAlgEquiv : F_p[σ] ≃ F_p[X]`. -/
theorem k2PolyField_eq_one_of_unique {σ : Type*} [Unique σ] {p : ℕ} (hp : p.Prime) {N : ℕ}
    (hN : 5 ≤ N) (h : k2PolyField_ConstStatement (ZMod p) N)
    (v : K2n N (MvPolynomial σ (ZMod p))) : v = 1 := by
  have hv : K2Map (MvPolynomial.uniqueAlgEquiv (ZMod p) σ).toRingEquiv.toRingHom v = 1 :=
    eq_one_of_K2_eq_bot (k2PolyField_K2_eq_bot_of_const hp hN h) _
  rw [← K2Map_K2Map_of_comp_eq_id _ _
      (MvPolynomial.uniqueAlgEquiv (ZMod p) σ).toRingEquiv.symm_toRingHom_comp_toRingHom v,
    hv, map_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyField_eq_one_of_unique

end Const

end GroupApproximation.BooneHigman.Metabelian.ElemFP
