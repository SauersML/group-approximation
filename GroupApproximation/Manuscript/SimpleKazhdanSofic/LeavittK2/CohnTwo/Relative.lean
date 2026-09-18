import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.Quotient
import GroupApproximation.BooneHigman.SteinbergBasic.Naturality
import GroupApproximation.Leavitt.CongruenceSubgroups
import Mathlib.Data.Fin.Embedding
import GroupApproximation.Meta.AxiomGuard

/-!
# Relative lifting along `C_2 → L_k(1,2)`

Lane `sk-leavitt-18`, fourth module.  Write `π = toLeavitt k : C_2 → L` and
`I = (p) = pIdeal k`.

* `mem_pIdeal_of_toLeavitt_eq_zero`: `ker π ⊆ I`, read off from the
  isomorphism `C_2 / I ≃ L` of `Quotient.lean`.
* `sub_one_mem_pIdeal_of_map_eq_one`: a unit of `M_n(C_2)` that becomes `1`
  over `L` is congruent to `1` modulo `I`, entrywise.
* `relativeElementary_le_map_ker`: `EL_n(C_2, I)` (the normal closure in
  `EL_n(C_2)` of the roots with coefficients in `I`) lies in the image under
  `St_n(C_2) → EL_n(C_2)` of `ker (St_n(C_2) → St_n(L))`.  The image is normal
  because the projection is onto, and it contains the generators because
  `x_ij(a) ↦ x_ij(π a) = x_ij(0) = 1`.
* Two relabelling identities for Steinberg groups along `Fin.castLE`, checked on
  generators.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

namespace CohnTwo

section Field

variable (k : Type*) [Field k]

/-- `ker (C_2 → L) ⊆ (p)`. -/
theorem mem_pIdeal_of_toLeavitt_eq_zero {x : CohnTwo k} (hx : toLeavitt k x = 0) :
    x ∈ pIdeal k := by
  have h1 := DFunLike.congr_fun (leavittToQuotient_comp_quotientToLeavitt k)
    ((pIdeal k).ringCon.mkₐ k x)
  rw [AlgHom.comp_apply, AlgHom.id_apply, quotientToLeavitt_mk, hx, map_zero] at h1
  have h2 : (pIdeal k).ringCon.mkₐ k x = (pIdeal k).ringCon.mkₐ k 0 := by
    rw [map_zero]
    exact h1.symm
  have h3 := (RingCon.eq (pIdeal k).ringCon (a := x) (b := 0)).mp h2
  have h4 := (TwoSidedIdeal.rel_iff (pIdeal k) x 0).mp h3
  rwa [sub_zero] at h4

/-- A unit of `M_n(C_2)` mapping to `1` over `L` is `≡ 1` modulo `(p)`. -/
theorem sub_one_mem_pIdeal_of_map_eq_one {n : ℕ} (U : (Matrix (Fin n) (Fin n) (CohnTwo k))ˣ)
    (hU : elementaryMatrixUnitMap (toLeavitt k).toRingHom U = 1) (i j : Fin n) :
    ((U : Matrix (Fin n) (Fin n) (CohnTwo k)) - 1) i j ∈ pIdeal k := by
  refine mem_pIdeal_of_toLeavitt_eq_zero k ?_
  have h := congrArg
    (fun z : (Matrix (Fin n) (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra k))ˣ =>
      (z : Matrix (Fin n) (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra k)) i j) hU
  change toLeavitt k ((U : Matrix (Fin n) (Fin n) (CohnTwo k)) i j) =
    (1 : Matrix (Fin n) (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra k)) i j at h
  rw [Matrix.sub_apply, map_sub, h]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, sub_self]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero, sub_zero]

/-- `EL_n(C_2, (p)) ⊆ projection (ker (St_n(C_2) → St_n(L)))`. -/
theorem relativeElementary_le_map_ker (n : ℕ) :
    relativeElementary (Fin n) (pIdeal k) ≤
      (GroupApproximation.SteinbergGroup.ringMap (I := Fin n)
        (toLeavitt k).toRingHom).ker.map GroupApproximation.SteinbergGroup.projection := by
  haveI : ((GroupApproximation.SteinbergGroup.ringMap (I := Fin n)
      (toLeavitt k).toRingHom).ker.map GroupApproximation.SteinbergGroup.projection).Normal :=
    (MonoidHom.normal_ker _).map _ GroupApproximation.SteinbergGroup.projection_surjective
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨i, j, hij, a, ha, rfl⟩
  have ha0 : (toLeavitt k).toRingHom a = 0 :=
    (TwoSidedIdeal.mem_ker (toLeavitt k)).mp (pIdeal_le_ker k ha)
  refine Subgroup.mem_map.mpr ⟨GroupApproximation.SteinbergGroup.x i j hij a, ?_, ?_⟩
  · rw [MonoidHom.mem_ker, GroupApproximation.SteinbergGroup.ringMap_x, ha0,
      GroupApproximation.SteinbergGroup.x_zero]
  · exact GroupApproximation.SteinbergGroup.projection_x i j hij a

end Field

section Relabel

variable {R S : Type*} [Ring R] [Ring S]

/-- Relabelling along `Fin.castLE` commutes with coefficient maps. -/
theorem indexMap_castLE_ringMap (f : R →+* S) {n m : ℕ} (h : n ≤ m)
    (t : GroupApproximation.SteinbergGroup (Fin n) R) :
    GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h)
        (GroupApproximation.SteinbergGroup.ringMap f t) =
      GroupApproximation.SteinbergGroup.ringMap f
        (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) t) := by
  have hcomp : (GroupApproximation.SteinbergGroup.indexMap (R := S) (Fin.castLEEmb h)).comp
      (GroupApproximation.SteinbergGroup.ringMap (I := Fin n) f) =
      (GroupApproximation.SteinbergGroup.ringMap (I := Fin m) f).comp
        (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h)) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h)
        (GroupApproximation.SteinbergGroup.ringMap f (GroupApproximation.SteinbergGroup.x i j hij a)) =
      GroupApproximation.SteinbergGroup.ringMap f
        (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h)
          (GroupApproximation.SteinbergGroup.x i j hij a))
    rw [GroupApproximation.SteinbergGroup.ringMap_x, GroupApproximation.SteinbergGroup.indexMap_x,
      GroupApproximation.SteinbergGroup.indexMap_x, GroupApproximation.SteinbergGroup.ringMap_x]
  exact DFunLike.congr_fun hcomp t

/-- Two relabellings along `Fin.castLE` compose to one. -/
theorem indexMap_castLE_castLE {n m N : ℕ} (h : n ≤ m) (h' : m ≤ N)
    (t : GroupApproximation.SteinbergGroup (Fin n) R) :
    GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h')
        (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) t) =
      GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb (h.trans h')) t := by
  have hcomp : (GroupApproximation.SteinbergGroup.indexMap (R := R) (Fin.castLEEmb h')).comp
      (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h)) =
      GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb (h.trans h')) := by
    apply PresentedGroup.ext
    rintro ⟨i, j, hij, a⟩
    change GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h')
        (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h)
          (GroupApproximation.SteinbergGroup.x i j hij a)) =
      GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb (h.trans h'))
        (GroupApproximation.SteinbergGroup.x i j hij a)
    exact (congrArg (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h'))
        (GroupApproximation.SteinbergGroup.indexMap_x (Fin.castLEEmb h) i j hij a)).trans
      ((GroupApproximation.SteinbergGroup.indexMap_x (Fin.castLEEmb h') _ _ _ a).trans
        (GroupApproximation.SteinbergGroup.indexMap_x (Fin.castLEEmb (h.trans h')) i j hij a).symm)
  exact DFunLike.congr_fun hcomp t

end Relabel

end CohnTwo

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.mem_pIdeal_of_toLeavitt_eq_zero
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.sub_one_mem_pIdeal_of_map_eq_one
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.relativeElementary_le_map_ker
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.indexMap_castLE_ringMap
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.indexMap_castLE_castLE
