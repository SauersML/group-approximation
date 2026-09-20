import GroupApproximation.BooneHigmanLinear.RelGen.Statements
import Mathlib.RingTheory.Ideal.Quotient.Operations
import GroupApproximation.Meta.AxiomGuard

/-!
# L–S (4.4): the split of `St̄(A[X], M[X])` along evaluation at `0` (k2-poly H.L3)

Lane k2-hl3b. A. Lavrenov and S. Sinchuk, arXiv:1909.02637, §4.2, display (4.4):
`St̄(Φ, A[X], M[X]) = St̄(Φ, A, M) ⋉ K(A[X], M[X])`, because evaluation at `0` is split by the
constants, `ev₀ ∘ C = id`. This file proves it in type A over an index type `I`, in the element
form `Split44Statement` of `RelGen.Statements`: every `g ∈ St̄(A[X], M[X])` is `C(g(0)) · k` with
`g(0) ∈ St̄(A, M)` and `k ∈ K(A[X], M[X])`. No hypothesis on `A` is needed.

* `mem_relKer_iff_ringMap`: `g ∈ St̄(R, J)` iff `g ↦ 1` in `St_I(R/J)`.
* `ringMap_mem_relKer`: a ring map `f` with `J ≤ f⁻¹(J')` carries `St̄(R, J)` into `St̄(S, J')`,
  through `Ideal.quotientMap`.
* `evalZero_comp_C`, `ringMap_evalZero_C`: `ev₀ ∘ C = id`, on rings and on Steinberg groups.
* `polyIdeal_le_comap_evalZero`: `ev₀(M[X]) ⊆ M`.
* `split44 : Split44Statement`.
-/

namespace GroupApproximation.BooneHigmanLinear.RelGen

open GroupApproximation.SteinbergGroup

section Transport

variable {I : Type*} [Fintype I] [DecidableEq I] {R S : Type*} [CommRing R] [CommRing S]

/-- Membership in `St̄(R, J)`: the image in `St_I(R/J)` is trivial. -/
theorem mem_relKer_iff_ringMap {J : Ideal R} {g : SteinbergGroup I R} :
    g ∈ relKer I J ↔ ringMap (Ideal.Quotient.mk J) g = 1 :=
  K2Found.mem_relSt

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.mem_relKer_iff_ringMap

/-- A ring map `f` with `J ≤ f⁻¹(J')` carries `St̄(R, J)` into `St̄(S, J')`. -/
theorem ringMap_mem_relKer (f : R →+* S) {J : Ideal R} {J' : Ideal S} (hJ : J ≤ J'.comap f)
    {g : SteinbergGroup I R} (hg : g ∈ relKer I J) : ringMap f g ∈ relKer I J' := by
  have hg' : ringMap (Ideal.Quotient.mk J) g = 1 := mem_relKer_iff_ringMap.mp hg
  have key : (Ideal.Quotient.mk J').comp f =
      (Ideal.quotientMap J' f hJ).comp (Ideal.Quotient.mk J) :=
    (Ideal.quotientMap_comp_mk hJ).symm
  refine mem_relKer_iff_ringMap.mpr ?_
  calc ringMap (Ideal.Quotient.mk J') (ringMap f g)
      = ringMap ((Ideal.Quotient.mk J').comp f) g :=
        GroupApproximation.BooneHigman.SteinbergBasic.ringMap_ringMap _ _ _
    _ = ringMap ((Ideal.quotientMap J' f hJ).comp (Ideal.Quotient.mk J)) g := by rw [key]
    _ = ringMap (Ideal.quotientMap J' f hJ) (ringMap (Ideal.Quotient.mk J) g) :=
        (GroupApproximation.BooneHigman.SteinbergBasic.ringMap_ringMap _ _ _).symm
    _ = 1 := by rw [hg', map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ringMap_mem_relKer

end Transport

section Poly

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Type*} [CommRing A]

/-- `ev₀ ∘ C = id`. -/
theorem evalZero_comp_C :
    (Polynomial.evalRingHom 0 : Polynomial A →+* A).comp Polynomial.C = RingHom.id A :=
  RingHom.ext fun a => by simp

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.evalZero_comp_C

/-- `ev₀ ∘ C = id` on Steinberg groups: `C(u)(0) = u`. -/
theorem ringMap_evalZero_C (u : SteinbergGroup I A) :
    ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) (ringMap Polynomial.C u) = u := by
  calc ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) (ringMap Polynomial.C u)
      = ringMap ((Polynomial.evalRingHom 0 : Polynomial A →+* A).comp Polynomial.C) u :=
        GroupApproximation.BooneHigman.SteinbergBasic.ringMap_ringMap _ _ _
    _ = ringMap (RingHom.id A) u := by rw [evalZero_comp_C]
    _ = u := DFunLike.congr_fun GroupApproximation.BooneHigman.SteinbergBasic.ringMap_id u

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.ringMap_evalZero_C

/-- Evaluation at `0` carries `M[X]` into `M`. -/
theorem polyIdeal_le_comap_evalZero (M : Ideal A) :
    polyIdeal M ≤ M.comap (Polynomial.evalRingHom 0 : Polynomial A →+* A) := by
  refine Ideal.map_le_iff_le_comap.mpr fun a ha => ?_
  simpa using ha

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.polyIdeal_le_comap_evalZero

end Poly

/-- **L–S (4.4)**, element form: `g = C(g(0)) · k` with `g(0) ∈ St̄(A, M)` and
`k ∈ K(A[X], M[X])`. -/
theorem split44 : Split44Statement := by
  intro I _ _ A _ M g hg
  have h0 : ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) g ∈ relKer I M :=
    ringMap_mem_relKer (Polynomial.evalRingHom 0 : Polynomial A →+* A)
      (polyIdeal_le_comap_evalZero M) hg
  have hC : ringMap (Polynomial.C : A →+* Polynomial A)
      (ringMap (Polynomial.evalRingHom 0 : Polynomial A →+* A) g) ∈ relKer I (polyIdeal M) :=
    ringMap_mem_relKer (Polynomial.C : A →+* Polynomial A) (J' := polyIdeal M)
      Ideal.le_comap_map h0
  refine ⟨h0, Subgroup.mem_inf.mpr ⟨(relKer I (polyIdeal M)).mul_mem
    ((relKer I (polyIdeal M)).inv_mem hC) hg, ?_⟩⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, ringMap_evalZero_C]
  exact inv_mul_cancel _

#audit_axioms GroupApproximation.BooneHigmanLinear.RelGen.split44

end GroupApproximation.BooneHigmanLinear.RelGen
