import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import GroupApproximation.Meta.AxiomGuard

/-!
# `F_p[s_1, ..., s_k]` is a finitely presented quotient of `ℤ⟨s_1, ..., s_k⟩`

The ring map `polyQuotientMap p k : ℤ⟨Fin k⟩ → (ZMod p)[Fin k]` sends `ι s` to the variable
`X s`.  It is surjective (`polyQuotientMap_surjective`), and its kernel is the two-sided span of the
finite set `polyRelators p k = {p} ∪ {s t - t s}` (`ker_polyQuotientMap`).

Proof of the hard inclusion: in `Q = ℤ⟨Fin k⟩ / (polyRelators)` the generators commute, so every
element is central (`relQuotMk_mem_center`) and `p = 0`.  The universal properties of `ZMod p`
and of `MvPolynomial` give `polyLift : (ZMod p)[Fin k] → Q` with
`polyLift ∘ polyQuotientMap = relQuotMk` (`polyLift_comp`).  So
`ker polyQuotientMap ⊆ ker relQuotMk`, which is the span.  These last steps are in
`ElemFPPolyKernel`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

noncomputable section

variable (p k : ℕ)

/-- `ℤ⟨Fin k⟩ → (ZMod p)[Fin k]`, sending `ι s` to the variable `X s`. -/
def polyQuotientMap : FreeAlgebra ℤ (Fin k) →+* MvPolynomial (Fin k) (ZMod p) :=
  (FreeAlgebra.lift ℤ fun i => (MvPolynomial.X i : MvPolynomial (Fin k) (ZMod p))).toRingHom

theorem polyQuotientMap_ι (i : Fin k) :
    polyQuotientMap p k (FreeAlgebra.ι ℤ i) = MvPolynomial.X i :=
  FreeAlgebra.lift_ι_apply _ _

theorem polyQuotientMap_surjective : Function.Surjective (polyQuotientMap p k) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C a =>
      obtain ⟨r, rfl⟩ := ZMod.intCast_surjective a
      exact ⟨(r : FreeAlgebra ℤ (Fin k)), by simp only [map_intCast]⟩
  | add P Q hP hQ =>
      obtain ⟨x, hx⟩ := hP
      obtain ⟨y, hy⟩ := hQ
      exact ⟨x + y, by rw [map_add, hx, hy]⟩
  | mul_X P i hP =>
      obtain ⟨x, hx⟩ := hP
      exact ⟨x * FreeAlgebra.ι ℤ i, by rw [map_mul, hx, polyQuotientMap_ι]⟩

/-- The finitely many relators: `p` and the commutators of the generators. -/
def polyRelators : Set (FreeAlgebra ℤ (Fin k)) :=
  insert (p : FreeAlgebra ℤ (Fin k)) (Set.range fun ij : Fin k × Fin k =>
    FreeAlgebra.ι ℤ ij.1 * FreeAlgebra.ι ℤ ij.2 - FreeAlgebra.ι ℤ ij.2 * FreeAlgebra.ι ℤ ij.1)

theorem polyRelators_finite : (polyRelators p k).Finite :=
  Set.Finite.insert _ (Set.finite_range _)

theorem natCast_mem_polyRelators : (p : FreeAlgebra ℤ (Fin k)) ∈ polyRelators p k :=
  Set.mem_insert _ _

theorem comm_mem_polyRelators (i j : Fin k) :
    FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j - FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i ∈
      polyRelators p k :=
  Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩

theorem span_polyRelators_le_ker :
    TwoSidedIdeal.span (polyRelators p k) ≤ TwoSidedIdeal.ker (polyQuotientMap p k) := by
  rw [TwoSidedIdeal.span_le]
  rintro z (rfl | ⟨⟨i, j⟩, rfl⟩)
  · change (p : FreeAlgebra ℤ (Fin k)) ∈ TwoSidedIdeal.ker (polyQuotientMap p k)
    rw [TwoSidedIdeal.mem_ker, map_natCast]
    exact CharP.cast_eq_zero p
  · change FreeAlgebra.ι ℤ i * FreeAlgebra.ι ℤ j - FreeAlgebra.ι ℤ j * FreeAlgebra.ι ℤ i ∈
      TwoSidedIdeal.ker (polyQuotientMap p k)
    rw [TwoSidedIdeal.mem_ker, map_sub, map_mul, map_mul, polyQuotientMap_ι, polyQuotientMap_ι]
    exact sub_eq_zero.mpr (mul_comm _ _)

/-- The quotient ring `ℤ⟨Fin k⟩ / (polyRelators p k)`. -/
abbrev RelQuot : Type := (TwoSidedIdeal.span (polyRelators p k)).ringCon.Quotient

/-- The quotient map onto `RelQuot p k`. -/
def relQuotMk : FreeAlgebra ℤ (Fin k) →+* RelQuot p k :=
  (TwoSidedIdeal.span (polyRelators p k)).ringCon.mk'

theorem ker_relQuotMk :
    TwoSidedIdeal.ker (relQuotMk p k) = TwoSidedIdeal.span (polyRelators p k) :=
  TwoSidedIdeal.ker_ringCon_mk' _

theorem relQuotMk_surjective : Function.Surjective (relQuotMk p k) :=
  RingCon.mk'_surjective _

theorem relQuotMk_relator {z : FreeAlgebra ℤ (Fin k)} (hz : z ∈ polyRelators p k) :
    relQuotMk p k z = 0 := by
  have h : z ∈ TwoSidedIdeal.ker (relQuotMk p k) := by
    rw [ker_relQuotMk]
    exact TwoSidedIdeal.subset_span hz
  rwa [TwoSidedIdeal.mem_ker] at h

theorem relQuotMk_ι_comm (i j : Fin k) :
    Commute (relQuotMk p k (FreeAlgebra.ι ℤ i)) (relQuotMk p k (FreeAlgebra.ι ℤ j)) := by
  have h := relQuotMk_relator p k (comm_mem_polyRelators p k i j)
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

/-- All elements of the quotient commute. -/
theorem relQuotMk_commute (x y : FreeAlgebra ℤ (Fin k)) :
    Commute (relQuotMk p k x) (relQuotMk p k y) := by
  induction x using FreeAlgebra.induction with
  | grade0 r =>
      rw [eq_intCast (algebraMap ℤ (FreeAlgebra ℤ (Fin k))) r, map_intCast]
      exact Int.cast_commute r _
  | grade1 i =>
      induction y using FreeAlgebra.induction with
      | grade0 r =>
          rw [eq_intCast (algebraMap ℤ (FreeAlgebra ℤ (Fin k))) r, map_intCast]
          exact (Int.cast_commute r _).symm
      | grade1 j => exact relQuotMk_ι_comm p k i j
      | mul a b ha hb =>
          rw [map_mul]
          exact ha.mul_right hb
      | add a b ha hb =>
          rw [map_add]
          exact ha.add_right hb
  | mul a b ha hb =>
      rw [map_mul]
      exact ha.mul_left hb
  | add a b ha hb =>
      rw [map_add]
      exact ha.add_left hb

theorem relQuotMk_mem_center (x : FreeAlgebra ℤ (Fin k)) :
    relQuotMk p k x ∈ Subring.center (RelQuot p k) := by
  rw [Subring.mem_center_iff]
  intro g
  obtain ⟨y, rfl⟩ := relQuotMk_surjective p k g
  exact relQuotMk_commute p k y x

theorem relQuot_natCast_p : (p : RelQuot p k) = 0 := by
  have h := relQuotMk_relator p k (natCast_mem_polyRelators p k)
  rwa [map_natCast] at h

theorem center_natCast_p : (p : Subring.center (RelQuot p k)) = 0 :=
  Subtype.ext (relQuot_natCast_p p k)

end

end GroupApproximation.BooneHigman.Metabelian.ElemFP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyQuotientMap
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyQuotientMap_ι
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyQuotientMap_surjective
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyRelators
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.polyRelators_finite
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.natCast_mem_polyRelators
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.comm_mem_polyRelators
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.span_polyRelators_le_ker
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.RelQuot
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.relQuotMk
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.ker_relQuotMk
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.relQuotMk_surjective
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.relQuotMk_relator
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.relQuotMk_ι_comm
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.relQuotMk_commute
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.relQuotMk_mem_center
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.relQuot_natCast_p
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.center_natCast_p
