import GroupApproximation.Leavitt.CongruenceSubgroups
import Mathlib.RingTheory.Congruence.Defs
import Mathlib.Data.Matrix.Basic
import GroupApproximation.Meta.AxiomGuard

/-!
# `C_4(R, I)` is the preimage of the centre of `GL_4(R/I)`

`non_mf_groups_exist.tex`, proof of the binary example (tex lines 1193--1200):

> there is an ideal `I` of `R` with `EL_4(R,I) ≤ N ≤ C_4(R,I)`,
> where `EL_4(R,I)` is the normal closure in `EL_4(R)` of the
> elementary matrices `e_{ij}(a)` with `a ∈ I`, and `C_4(R,I)` is the
> preimage of the center of `GL_4(R/I)`.  (tex 1198--1200, census key `e4440282ed35`)

The census lists `GroupApproximation.relativeElementary` and
`GroupApproximation.congruenceSubgroup`.  The first is literally the printed
normal closure (`manuscriptSentence_relativeElementaryIsNormalClosure`, by
`rfl`).  The second is *defined* in the library as "congruent modulo `I`,
entrywise, to a scalar whose coefficient is central modulo `I`", which is not
the printed definition.  This module adds the printed object and proves the
two agree.

## The printed object

* `quotientUnitsMap ι I : GL_ι(R) →* GL_ι(R/I)` is `Units.map` of the
  entrywise reduction `Matrix ι ι R →+* Matrix ι ι (R/I)`, where `R/I` is
  `I.ringCon.Quotient`.
* `quotientCenterPreimage ι I` is the preimage under this map of
  `Subgroup.center GL_ι(R/I)`.

## Proof route

For `1 < #ι` the centre of `GL_ι(S)` is `congruenceSubgroup ι (⊥ : S)`
(`congruenceSubgroup_bot`, applied to `S = R/I`).  Reduction modulo `I` is
surjective, so the scalar `λ' ∈ S` lifts to `λ ∈ R`.  Two facts then transfer
the conditions entry by entry:

* `mk'_eq_mk'_iff`: `[a] = [b]` in `R/I` iff `a - b ∈ I`;
* `entry_mem_bot_iff`: the `(i, j)` entry of `ū - λ̄·1` vanishes iff the
  `(i, j)` entry of `u - λ·1` lies in `I`.

"`λ̄` is central in `R/I`" is exactly "`λ` is central modulo `I`".

## Endpoints

* `manuscriptSentence_congruenceSubgroupIsCenterPreimage` : for every ring `R`
  and every two-sided ideal `I`,
  `C_4(R,I) = (GL_4(R) → GL_4(R/I))⁻¹ (Z(GL_4(R/I)))`.
* `manuscriptSentence_congruenceSubgroupIsCenterPreimageGeneral` : the same
  equality for every finite index type with at least two elements.
* `manuscriptSentence_relativeElementaryIsNormalClosure` : `EL_4(R,I)` is the
  normal closure in `EL_4(R)` of the `e_{ij}(a)` with `a ∈ I`.
-/

namespace GroupApproximation.Manuscript.NonMF.AuditBinaryUnits

noncomputable section

section Reduction

variable {R : Type*} [Ring R]

/-- Reduction modulo a two-sided ideal identifies exactly the elements whose
difference lies in the ideal. -/
theorem mk'_eq_mk'_iff (I : TwoSidedIdeal R) (a b : R) :
    I.ringCon.mk' a = I.ringCon.mk' b ↔ a - b ∈ I :=
  (RingCon.eq I.ringCon).trans (TwoSidedIdeal.rel_iff I a b)

end Reduction

section Printed

variable (ι : Type*) [Fintype ι] [DecidableEq ι] {R : Type*} [Ring R]

/-- The entrywise reduction `GL_ι(R) → GL_ι(R/I)`. -/
def quotientUnitsMap (I : TwoSidedIdeal R) :
    (Matrix ι ι R)ˣ →* (Matrix ι ι I.ringCon.Quotient)ˣ :=
  Units.map (RingHom.mapMatrix (m := ι) I.ringCon.mk').toMonoidHom

/-- **The printed `C_ι(R, I)`**: the preimage of the centre of `GL_ι(R/I)`. -/
def quotientCenterPreimage (I : TwoSidedIdeal R) : Subgroup (Matrix ι ι R)ˣ :=
  (Subgroup.center (Matrix ι ι I.ringCon.Quotient)ˣ).comap (quotientUnitsMap ι I)

end Printed

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [Ring R]

theorem quotientUnitsMap_apply (I : TwoSidedIdeal R) (u : (Matrix ι ι R)ˣ) (i j : ι) :
    ((quotientUnitsMap ι I u : (Matrix ι ι I.ringCon.Quotient)ˣ) :
        Matrix ι ι I.ringCon.Quotient) i j
      = I.ringCon.mk' ((u : Matrix ι ι R) i j) :=
  rfl

/-- The entrywise condition at level `0` over `R/I` is the entrywise condition
at level `I` over `R`. -/
theorem entry_mem_bot_iff (I : TwoSidedIdeal R) (u : (Matrix ι ι R)ˣ) (lam : R)
    (i j : ι) :
    (((quotientUnitsMap ι I u : (Matrix ι ι I.ringCon.Quotient)ˣ) :
          Matrix ι ι I.ringCon.Quotient)
        - Matrix.diagonal fun _ : ι ↦ I.ringCon.mk' lam) i j
        ∈ (⊥ : TwoSidedIdeal I.ringCon.Quotient)
      ↔ ((u : Matrix ι ι R) - Matrix.diagonal fun _ : ι ↦ lam) i j ∈ I := by
  have hdiag : (Matrix.diagonal fun _ : ι ↦ I.ringCon.mk' lam) i j
      = I.ringCon.mk' ((Matrix.diagonal fun _ : ι ↦ lam) i j) := by
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ hij]
      exact (map_zero I.ringCon.mk').symm
  rw [TwoSidedIdeal.mem_bot, Matrix.sub_apply, Matrix.sub_apply, sub_eq_zero, hdiag,
    quotientUnitsMap_apply]
  exact mk'_eq_mk'_iff I _ _

/-- **The printed `C_ι(R, I)` is the library's `congruenceSubgroup ι I`**, for
every ring `R`, every two-sided ideal `I`, and `#ι ≥ 2`. -/
theorem quotientCenterPreimage_eq_congruenceSubgroup (hcard : 1 < Fintype.card ι)
    (I : TwoSidedIdeal R) :
    quotientCenterPreimage ι I = congruenceSubgroup ι I := by
  obtain ⟨i₀, -, -⟩ := Fintype.exists_pair_of_one_lt_card hcard
  ext u
  rw [quotientCenterPreimage, Subgroup.mem_comap,
    ← congruenceSubgroup_bot (R := I.ringCon.Quotient) hcard i₀,
    mem_congruenceSubgroup, mem_congruenceSubgroup]
  constructor
  · rintro ⟨lam', hlam', hu⟩
    obtain ⟨lam, rfl⟩ := I.ringCon.mk'_surjective lam'
    refine ⟨lam, mem_relativeCenter.mpr fun x ↦ ?_,
      fun i j ↦ (entry_mem_bot_iff I u lam i j).mp (hu i j)⟩
    have hx := mem_relativeCenter.mp hlam' (I.ringCon.mk' x)
    rw [TwoSidedIdeal.mem_bot, sub_eq_zero, ← map_mul I.ringCon.mk',
      ← map_mul I.ringCon.mk', mk'_eq_mk'_iff] at hx
    exact hx
  · rintro ⟨lam, hlam, hu⟩
    refine ⟨I.ringCon.mk' lam, mem_relativeCenter.mpr fun x' ↦ ?_,
      fun i j ↦ (entry_mem_bot_iff I u lam i j).mpr (hu i j)⟩
    obtain ⟨x, rfl⟩ := I.ringCon.mk'_surjective x'
    rw [TwoSidedIdeal.mem_bot, sub_eq_zero, ← map_mul I.ringCon.mk',
      ← map_mul I.ringCon.mk', mk'_eq_mk'_iff]
    exact mem_relativeCenter.mp hlam x

end Transfer

section Endpoints

variable {R : Type*} [Ring R]

/-- **Printed (tex 1200):** "`C_4(R,I)` is the preimage of the center of
`GL_4(R/I)`."  The library's `congruenceSubgroup (Fin 4) I` is that preimage. -/
theorem manuscriptSentence_congruenceSubgroupIsCenterPreimage (I : TwoSidedIdeal R) :
    congruenceSubgroup (Fin 4) I = quotientCenterPreimage (Fin 4) I :=
  (quotientCenterPreimage_eq_congruenceSubgroup
    (by rw [Fintype.card_fin]; decide) I).symm

#audit_axioms manuscriptSentence_congruenceSubgroupIsCenterPreimage

/-- The same identification at every size `n ≥ 2`. -/
theorem manuscriptSentence_congruenceSubgroupIsCenterPreimageGeneral
    {ι : Type*} [Fintype ι] [DecidableEq ι] (hcard : 1 < Fintype.card ι)
    (I : TwoSidedIdeal R) :
    congruenceSubgroup ι I = quotientCenterPreimage ι I :=
  (quotientCenterPreimage_eq_congruenceSubgroup hcard I).symm

#audit_axioms manuscriptSentence_congruenceSubgroupIsCenterPreimageGeneral

/-- **Printed (tex 1198--1199):** "`EL_4(R,I)` is the normal closure in
`EL_4(R)` of the elementary matrices `e_{ij}(a)` with `a ∈ I`." -/
theorem manuscriptSentence_relativeElementaryIsNormalClosure (I : TwoSidedIdeal R) :
    relativeElementary (Fin 4) I
      = Subgroup.normalClosure
          {g : elementaryGroup (Fin 4) R |
            ∃ (i j : Fin 4) (hij : i ≠ j) (a : R), a ∈ I ∧ g = elGen i j hij a} :=
  rfl

#audit_axioms manuscriptSentence_relativeElementaryIsNormalClosure

end Endpoints

end

end GroupApproximation.Manuscript.NonMF.AuditBinaryUnits
