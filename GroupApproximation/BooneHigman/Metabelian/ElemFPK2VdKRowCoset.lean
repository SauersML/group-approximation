import GroupApproximation.BooneHigman.Metabelian.ElemFPK2VdKRowCanonical
import Mathlib.GroupTheory.Coset.Defs
import GroupApproximation.Meta.AxiomGuard

/-!
# Row data from injectivity of the parabolic map

Lane `bh-met-62`.  Let `P̃ = vdkRowParSubgroup n R ≤ St_{n+1}(R)` and let `X = P̃ \ St_{n+1}(R)`
be its right cosets, `VdKRowCoset n R`.  Choose a representative of each coset.

* `vdkRowCosetMap : VdKΩ n R X → St_{n+1}(R)`, `(v, g, ξ) ↦ vdkRowPar (v, g) · out ξ`.
  It is always surjective (`vdkRowCosetMap_surjective`).  It is injective once `vdkRowPar` is
  injective (`vdkRowCosetMap_injective`).
* `vdkRowCosetEquiv hinj`: the resulting bijection.  It intertwines `vdkAct` with left
  multiplication by `stab` (`vdkRowCosetEquiv_act`) and `vdkCol` with left multiplication by
  `x_{i,last}` (`vdkRowCosetEquiv_col`).
* `vdkRowDataOfInjective hinj : VdKRowData n R X`, by `VdKRowGroupData.toRowData` applied to
  `vdkRowCanonical`, over any ring.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2 (colRoot projectionMatrix)
open scoped Matrix

variable (n : ℕ) (R : Type*) [Ring R]

/-- The right cosets `P̃ \ St_{n+1}(R)` of the image of the parabolic map. -/
abbrev VdKRowCoset : Type _ := Quotient (QuotientGroup.rightRel (vdkRowParSubgroup n R))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.VdKRowCoset

variable {n R}

/-- Multiplying on the left by an element of `P̃` does not change the right coset. -/
theorem vdkRowCoset_mk_mul (p : (Fin n → R) × St n R) (h : St (n + 1) R) :
    Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R)) (vdkRowPar p * h) =
      Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R)) h :=
  Quotient.eq.mpr (QuotientGroup.rightRel_apply.mpr (by
    rw [mul_inv_rev, mul_inv_cancel_left]
    exact (vdkRowParSubgroup n R).inv_mem ((mem_vdkRowParSubgroup _).mpr ⟨p, rfl⟩)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCoset_mk_mul

/-- The map `(v, g, ξ) ↦ vdkRowPar (v, g) · out ξ`. -/
noncomputable def vdkRowCosetMap (w : VdKΩ n R (VdKRowCoset n R)) : St (n + 1) R :=
  vdkRowPar (w.1, w.2.1) * Quotient.out w.2.2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCosetMap

theorem vdkRowCosetMap_apply (v : Fin n → R) (g : St n R) (ξ : VdKRowCoset n R) :
    vdkRowCosetMap (v, g, ξ) = vdkRowPar (v, g) * Quotient.out ξ :=
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCosetMap_apply

theorem vdkRowCosetMap_surjective : Function.Surjective (vdkRowCosetMap (n := n) (R := R)) := by
  intro h
  obtain ⟨⟨v, g⟩, hp⟩ := (mem_vdkRowParSubgroup _).mp (QuotientGroup.rightRel_apply.mp
    (Quotient.mk_out (s := QuotientGroup.rightRel (vdkRowParSubgroup n R)) h))
  refine ⟨(v, g, Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R)) h), ?_⟩
  rw [vdkRowCosetMap_apply, hp, inv_mul_cancel_right]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCosetMap_surjective

theorem vdkRowCosetMap_injective (hinj : Function.Injective (vdkRowPar (n := n) (R := R))) :
    Function.Injective (vdkRowCosetMap (n := n) (R := R)) := by
  rintro ⟨v, g, ξ⟩ ⟨v', g', ξ'⟩ h
  rw [vdkRowCosetMap_apply, vdkRowCosetMap_apply] at h
  have h2 := congrArg (Quotient.mk (QuotientGroup.rightRel (vdkRowParSubgroup n R))) h
  rw [vdkRowCoset_mk_mul, vdkRowCoset_mk_mul, Quotient.out_eq, Quotient.out_eq] at h2
  subst h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (hinj (mul_right_cancel h))
  rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCosetMap_injective

/-- The bijection `VdKΩ n R X ≃ St_{n+1}(R)`, given injectivity of the parabolic map. -/
noncomputable def vdkRowCosetEquiv (hinj : Function.Injective (vdkRowPar (n := n) (R := R))) :
    VdKΩ n R (VdKRowCoset n R) ≃ St (n + 1) R :=
  Equiv.ofBijective vdkRowCosetMap ⟨vdkRowCosetMap_injective hinj, vdkRowCosetMap_surjective⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCosetEquiv

theorem vdkRowCosetEquiv_act (hinj : Function.Injective (vdkRowPar (n := n) (R := R)))
    (s : St n R) (w : VdKΩ n R (VdKRowCoset n R)) :
    vdkRowCosetEquiv hinj (vdkAct (VdKRowCoset n R) s w) =
      (vdkRowCanonical n R).act s * vdkRowCosetEquiv hinj w := by
  obtain ⟨v, g, ξ⟩ := w
  change vdkRowPar (projectionMatrix s *ᵥ v, s * g) * Quotient.out ξ =
    stab n R s * (vdkRowPar (v, g) * Quotient.out ξ)
  rw [vdkRowPar_stab, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCosetEquiv_act

theorem vdkRowCosetEquiv_col (hinj : Function.Injective (vdkRowPar (n := n) (R := R)))
    (i : Fin n) (a : R) (w : VdKΩ n R (VdKRowCoset n R)) :
    vdkRowCosetEquiv hinj (vdkCol (VdKRowCoset n R) i a w) =
      (vdkRowCanonical n R).col i a * vdkRowCosetEquiv hinj w := by
  obtain ⟨v, g, ξ⟩ := w
  change vdkRowPar (v + Pi.single i a, g) * Quotient.out ξ =
    colRoot i a * (vdkRowPar (v, g) * Quotient.out ξ)
  rw [vdkRowPar_col, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowCosetEquiv_col

/-- **Row data from injectivity**: over any ring, if the parabolic map is injective, then the
right cosets of its image carry van der Kallen row data. -/
noncomputable def vdkRowDataOfInjective (hinj : Function.Injective (vdkRowPar (n := n) (R := R))) :
    VdKRowData n R (VdKRowCoset n R) :=
  (vdkRowCanonical n R).toRowData (vdkRowCosetEquiv hinj) (vdkRowCosetEquiv_act hinj)
    (vdkRowCosetEquiv_col hinj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkRowDataOfInjective

end GroupApproximation.BooneHigman.Metabelian.ElemFP
