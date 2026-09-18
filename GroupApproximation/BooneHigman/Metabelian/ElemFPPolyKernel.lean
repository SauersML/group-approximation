import GroupApproximation.BooneHigman.Metabelian.ElemFPPolyPresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# The kernel of `ℤ⟨Fin k⟩ → (ZMod p)[Fin k]` is finitely generated

Continuation of `ElemFPPolyPresentation`.  The center of the relator quotient
`Q = ℤ⟨Fin k⟩ / (polyRelators p k)` is a commutative ring with `p = 0` that contains the images
of the generators.  So there are ring maps `zmodToCenter : ZMod p → Z(Q)` and
`polyLift : (ZMod p)[Fin k] → Q`, and `polyLift ∘ polyQuotientMap = relQuotMk` (`polyLift_comp`).
Hence `ker polyQuotientMap = span (polyRelators p k)` (`ker_polyQuotientMap`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

noncomputable section

variable (p k : ℕ)

/-- `ZMod p → Z(Q)`, through `ℤ / (p) ≃ ZMod p`. -/
def zmodToCenter : ZMod p →+* Subring.center (RelQuot p k) :=
  (Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom (Subring.center (RelQuot p k)))
    (fun a ha => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [map_mul, map_natCast, center_natCast_p, zero_mul])).comp
    (Int.quotientSpanNatEquivZMod p).symm.toRingHom

/-- The images of the generators, as central elements of `Q`. -/
def centerGen (i : Fin k) : Subring.center (RelQuot p k) :=
  ⟨relQuotMk p k (FreeAlgebra.ι ℤ i), relQuotMk_mem_center p k _⟩

/-- `(ZMod p)[Fin k] → Q`, sending `X s` to the class of `ι s`. -/
def polyLift : MvPolynomial (Fin k) (ZMod p) →+* RelQuot p k :=
  (Subring.center (RelQuot p k)).subtype.comp
    (MvPolynomial.eval₂Hom (zmodToCenter p k) (centerGen p k))

theorem polyLift_comp (z : FreeAlgebra ℤ (Fin k)) :
    polyLift p k (polyQuotientMap p k z) = relQuotMk p k z := by
  induction z using FreeAlgebra.induction with
  | grade0 r => simp only [eq_intCast, map_intCast]
  | grade1 i =>
      rw [polyQuotientMap_ι]
      exact congrArg Subtype.val (MvPolynomial.eval₂Hom_X' (zmodToCenter p k) (centerGen p k) i)
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

/-- The kernel of `ℤ⟨Fin k⟩ → (ZMod p)[Fin k]` is the two-sided span of `polyRelators p k`. -/
theorem ker_polyQuotientMap :
    TwoSidedIdeal.ker (polyQuotientMap p k) = TwoSidedIdeal.span (polyRelators p k) := by
  apply le_antisymm
  · intro z hz
    rw [TwoSidedIdeal.mem_ker] at hz
    have h : z ∈ TwoSidedIdeal.ker (relQuotMk p k) := by
      rw [TwoSidedIdeal.mem_ker, ← polyLift_comp p k z, hz, map_zero]
    rwa [ker_relQuotMk] at h
  · exact span_polyRelators_le_ker p k

end

end GroupApproximation.BooneHigman.Metabelian.ElemFP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.zmodToCenter
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.centerGen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyLift
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyLift_comp
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.ker_polyQuotientMap
