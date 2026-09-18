import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGtOneEndpoint
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngTorusOne
import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGen
import GroupApproximation.Meta.AxiomGuard

/-!
# The localisation map `ℤ[1/m] → ℤ[1/(mp)]` and `K₂` transport (lane `bh-met-93s`, part 1)

Infrastructure for the prime induction behind `czK2FngGtOne_RankThreeStatement`.

* `czK2FngGtOneRank3_locMap m p : ℤ[1/m] →+* ℤ[1/(mp)]` is the canonical map (`m` divides
  `mp`, so `m` is a unit in `ℤ[1/(mp)]`).  It is injective when `mp ≠ 0`
  (`czK2FngGtOneRank3_locMap_injective`).
* `czK2FngGtOneRank3_elemMap_injective`: an injective coefficient map gives an injective map
  of elementary groups.
* `czK2FngGtOneRank3_fng_of_step`: if `K₂(3, R)` is finitely normally generated and
  `K₂(3, S)` lies in the normal closure of `φ(K₂(3, R))` together with a finite subset `s` of
  `K₂(3, S)`, then `K₂(3, S)` is finitely normally generated.

Everything here is proved outright.  There are no hypotheses and no literature inputs.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

/-- `m` is a unit in `ℤ[1/(mp)]`. -/
theorem czK2FngGtOneRank3_isUnit (m p : ℕ) :
    IsUnit (algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) (m : ℤ)) :=
  IsLocalization.Away.isUnit_of_dvd ((m * p : ℕ) : ℤ) ⟨(p : ℤ), Nat.cast_mul m p⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_isUnit

/-- The canonical localisation map `ℤ[1/m] → ℤ[1/(mp)]`. -/
noncomputable def czK2FngGtOneRank3_locMap (m p : ℕ) :
    Localization.Away (m : ℤ) →+* Localization.Away ((m * p : ℕ) : ℤ) :=
  IsLocalization.Away.lift (m : ℤ) (czK2FngGtOneRank3_isUnit m p)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_locMap

/-- The localisation map is the identity on integers. -/
theorem czK2FngGtOneRank3_locMap_algebraMap (m p : ℕ) (a : ℤ) :
    czK2FngGtOneRank3_locMap m p (algebraMap ℤ (Localization.Away (m : ℤ)) a) =
      algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ)) a :=
  IsLocalization.Away.lift_eq (m : ℤ) (czK2FngGtOneRank3_isUnit m p) a

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_locMap_algebraMap

/-- The localisation map is injective when `mp ≠ 0`. -/
theorem czK2FngGtOneRank3_locMap_injective (m p : ℕ) (hmp : m * p ≠ 0) :
    Function.Injective (czK2FngGtOneRank3_locMap m p) := by
  have hinj : Function.Injective (algebraMap ℤ (Localization.Away ((m * p : ℕ) : ℤ))) :=
    IsLocalization.injective (Localization.Away ((m * p : ℕ) : ℤ))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (Nat.cast_ne_zero.mpr hmp))
  refine IsLocalization.injective_of_map_algebraMap_zero (M := Submonoid.powers (m : ℤ))
    (Localization.Away (m : ℤ)) (czK2FngGtOneRank3_locMap m p) fun a ha ↦ ?_
  rw [czK2FngGtOneRank3_locMap_algebraMap] at ha
  have ha0 : a = 0 := hinj (by rw [ha, map_zero])
  rw [ha0, map_zero]

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_locMap_injective

/-- An injective coefficient map induces an injective map of elementary groups. -/
theorem czK2FngGtOneRank3_elemMap_injective {ι R S : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] [Ring S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (elementaryGroupMap (ι := ι) f) := by
  intro g h hgh
  apply Subtype.ext
  have hmat : Function.Injective (f.mapMatrix.toMonoidHom : Matrix ι ι R →* Matrix ι ι S) :=
    fun a b hab ↦ Matrix.map_injective hf hab
  apply Units.map_injective hmat
  exact congrArg Subtype.val hgh

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_elemMap_injective

/-- **Transport of finite normal generation along a coefficient map.**  If `K₂(3, R)` is
finitely normally generated and `K₂(3, S)` lies in the normal closure of `φ(K₂(3, R))` together
with a finite subset `s ⊆ K₂(3, S)`, then `K₂(3, S)` is finitely normally generated. -/
theorem czK2FngGtOneRank3_fng_of_step {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hR : (K2 (Fin 3) R).IsFinitelyNormallyGenerated)
    (hstep : ∃ s : Set (SteinbergGroup (Fin 3) S), s.Finite ∧ s ⊆ K2 (Fin 3) S ∧
      K2 (Fin 3) S ≤ Subgroup.normalClosure
        (ringMap φ '' (K2 (Fin 3) R : Set (SteinbergGroup (Fin 3) R)) ∪ s)) :
    (K2 (Fin 3) S).IsFinitelyNormallyGenerated := by
  obtain ⟨t, htfin, ht⟩ := hR
  obtain ⟨s, hsfin, hsK, hle⟩ := hstep
  refine ⟨ringMap φ '' t ∪ s, (htfin.image _).union hsfin, le_antisymm ?_ ?_⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ (⟨u, hu, rfl⟩ | hu)
    · have hu' : u ∈ K2 (Fin 3) R := by
        rw [← ht]
        exact Subgroup.subset_normalClosure hu
      exact ringMap_mem_K2 φ hu'
    · exact hsK hu
  · refine hle.trans (Subgroup.normalClosure_le_normal ?_)
    rintro _ (⟨u, hu, rfl⟩ | hu)
    · have hu' : u ∈ Subgroup.normalClosure t := by
        rw [ht]
        exact hu
      exact Subgroup.normalClosure_mono Set.subset_union_left
        (Subgroup.map_normalClosure_le t (ringMap φ) (Subgroup.mem_map_of_mem _ hu'))
    · exact Subgroup.subset_normalClosure (Set.subset_union_right hu)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngGtOneRank3_fng_of_step

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
