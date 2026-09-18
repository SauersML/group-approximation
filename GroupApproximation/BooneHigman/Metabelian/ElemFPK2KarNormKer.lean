import GroupApproximation.BooneHigman.Metabelian.ElemFPK2KarNormHard
import GroupApproximation.Meta.AxiomGuard

/-!
# The kernel of `ev₀ : St(ι, R[X]) → St(ι, R)`

Lane `bh-met-92f`.  `ev₀` is split by `C : St(ι, R) → St(ι, R[X])`.  Let `N` be a normal subgroup
that contains every `x_ij(h)` with `h(0) = 0`.  Then the map `St(ι, R[X]) → St(ι, R[X]) / N`
factors through `C ∘ ev₀`: on a generator, `x_ij(C (h(0)))⁻¹ x_ij(h) = x_ij(h - C (h(0))) ∈ N`.
Hence `ker ev₀ ≤ N` (`k2KarNorm_ker_le`), and so
`ker ev₀ = normalClosure {x_ij(h) : h(0) = 0}` (`k2KarNorm_ker_eq_normalClosure`).
With a third index, `ker ev₀ ≤ H(X R[X])` (`k2KarNorm_ker_le_H`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

section KarNormKer

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Every normal subgroup that contains all `x_ij(h)` with `h(0) = 0` contains `ker ev₀`. -/
theorem k2KarNorm_ker_le (N : Subgroup (SteinbergGroup ι (Polynomial R))) [N.Normal]
    (hN : ∀ (i j : ι) (hij : i ≠ j) (h : Polynomial R), h.eval 0 = 0 → x i j hij h ∈ N) :
    (ringMap (I := ι) (Polynomial.evalRingHom (0 : R))).ker ≤ N := by
  have key : (QuotientGroup.mk' N).comp ((ringMap (I := ι) Polynomial.C).comp
      (ringMap (I := ι) (Polynomial.evalRingHom (0 : R)))) = QuotientGroup.mk' N := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, h⟩
    change QuotientGroup.mk' N (ringMap Polynomial.C
      (ringMap (Polynomial.evalRingHom (0 : R)) (x i j hij h))) = QuotientGroup.mk' N (x i j hij h)
    rw [ringMap_x, ringMap_x, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, ← x_neg, x_mul]
    apply hN
    rw [Polynomial.eval_add, Polynomial.eval_neg, Polynomial.eval_C, Polynomial.coe_evalRingHom,
      neg_add_cancel]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have e := DFunLike.congr_fun key y
  simp only [MonoidHom.comp_apply, hy, map_one] at e
  exact (QuotientGroup.eq_one_iff y).mp e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_ker_le

end KarNormKer

section KarNormPolyGens

/-- The generators `x_ij(h)`, `h(0) = 0`, of `ker ev₀` as a normal subgroup. -/
def k2KarNorm_polyGens (ι R : Type*) [Fintype ι] [DecidableEq ι] [CommRing R] :
    Set (SteinbergGroup ι (Polynomial R)) :=
  {g | ∃ i j : ι, ∃ hij : i ≠ j, ∃ h : Polynomial R, h.eval 0 = 0 ∧ x i j hij h = g}

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_polyGens

end KarNormPolyGens

section KarNormKer2

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- **`ker ev₀` is the normal closure of `{x_ij(h) : h(0) = 0}`** (any index type). -/
theorem k2KarNorm_ker_eq_normalClosure :
    (ringMap (I := ι) (Polynomial.evalRingHom (0 : R))).ker =
      Subgroup.normalClosure (k2KarNorm_polyGens ι R) := by
  apply le_antisymm
  · exact k2KarNorm_ker_le (Subgroup.normalClosure (k2KarNorm_polyGens ι R))
      fun i j hij h h0 ↦ Subgroup.subset_normalClosure ⟨i, j, hij, h, h0, rfl⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨i, j, hij, h, h0, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ringMap_x, Polynomial.coe_evalRingHom, h0, x_zero]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_ker_eq_normalClosure

/-- With a third index, `ker ev₀ ≤ H(J₀)`, where `J₀ = ker (eval 0) = X R[X]`. -/
theorem k2KarNorm_ker_le_H (h3 : ∀ i j : ι, ∃ m : ι, m ≠ i ∧ m ≠ j) :
    (ringMap (I := ι) (Polynomial.evalRingHom (0 : R))).ker ≤
      k2KarNorm_H ι (RingHom.ker (Polynomial.evalRingHom (0 : R))) := by
  haveI := k2KarNorm_H_normal (J := RingHom.ker (Polynomial.evalRingHom (0 : R))) h3
  refine k2KarNorm_ker_le _ fun i j hij h h0 ↦ k2KarNorm_x_mem i j hij ?_
  rw [RingHom.mem_ker, Polynomial.coe_evalRingHom]
  exact h0

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2KarNorm_ker_le_H

end KarNormKer2

end GroupApproximation.BooneHigman.Metabelian.ElemFP
