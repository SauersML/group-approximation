import GroupApproximation.Sofic.MarkedCompressionGroup
import GroupApproximation.Sofic.SoficTelescope
import Mathlib.GroupTheory.Commensurable

/-!
# Finite telescope-level orbits

Let `alpha : Gamma -> Gamma` be injective with finite-index range.  The level
copies in its mapping telescope are mutually commensurable.  After adjoining
the shift, the level-zero copy is commensurated by the whole vertical group.
It follows that every telescope level has finite orbits on the left-coset
space of the level-zero copy.

This is the geometric half of the sofic Clifford-witness argument.  Combined
with `FiniteOrbitInvariantKernel`, it produces finite invariant lamp groups
without choosing normal forms in the presented Clifford group.
-/

namespace GroupApproximation
namespace MappingTelescopeFiniteOrbits

open MappingTelescope MarkedCompression SemidirectProduct
open scoped Pointwise

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- Successive telescope levels have the same relative index as the range of
the compressing endomorphism. -/
theorem level_succ_relIndex_eq (n : ℕ) :
    (level α hα n).range.relIndex (level α hα (n + 1)).range =
      α.range.index := by
  have hn : (level α hα n).range =
      α.range.map (level α hα (n + 1)) := by
    rw [← MonoidHom.range_comp, level_succ_comp]
  have hs : (level α hα (n + 1)).range =
      (⊤ : Subgroup Γ).map (level α hα (n + 1)) := MonoidHom.range_eq_map _
  rw [hn, hs,
    Subgroup.relIndex_map_map_of_injective _ _ (level_injective α hα (n + 1)),
    Subgroup.relIndex_top_right]

/-- Every lower telescope level has finite relative index in every higher
level. -/
theorem level_relIndex_ne_zero [α.range.FiniteIndex] {n m : ℕ} (hnm : n ≤ m) :
    (level α hα n).range.relIndex (level α hα m).range ≠ 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  induction k with
  | zero => simp
  | succ k ih =>
      apply Subgroup.relIndex_ne_zero_trans
        (ih (Nat.le_add_right n k))
      rw [show n + (k + 1) = (n + k) + 1 from (Nat.add_assoc n k 1).symm,
        level_succ_relIndex_eq]
      exact Subgroup.FiniteIndex.index_ne_zero

/-- The level-zero copy and every telescope level are commensurable. -/
theorem level_commensurable_zero [α.range.FiniteIndex] (n : ℕ) :
    Subgroup.Commensurable (level α hα n).range (level α hα 0).range := by
  have hle : (level α hα 0).range ≤ (level α hα n).range :=
    fun _ h ↦ by
      obtain ⟨x, rfl⟩ := h
      exact level_mem_range_of_le α hα (Nat.zero_le n) x
  refine ⟨?_, level_relIndex_ne_zero α hα (Nat.zero_le n)⟩
  rw [Subgroup.relIndex_eq_one.mpr hle]
  exact one_ne_zero

/-- The copy of the base group inside the vertical semidirect product. -/
abbrev baseSubgroup : Subgroup (Vertical α hα) :=
  (iotaVertical α hα).range

/-- The copy of telescope level `n` inside the vertical group. -/
abbrev verticalLevel (n : ℕ) : Subgroup (Vertical α hα) :=
  ((inl : Telescope α hα →* Vertical α hα).comp (level α hα n)).range

theorem verticalLevel_eq_map (n : ℕ) :
    verticalLevel α hα n = (level α hα n).range.map
      (inl : Telescope α hα →* Vertical α hα) :=
  MonoidHom.range_comp _ _

theorem baseSubgroup_eq_map :
    baseSubgroup α hα = (level α hα 0).range.map
      (inl : Telescope α hα →* Vertical α hα) :=
  MonoidHom.range_comp _ _

theorem baseSubgroup_eq_map_top :
    baseSubgroup α hα = (⊤ : Subgroup Γ).map (iotaVertical α hα) :=
  MonoidHom.range_eq_map _

/-- Vertical telescope levels remain commensurable with the vertical base. -/
theorem verticalLevel_commensurable_base [α.range.FiniteIndex] (n : ℕ) :
    Subgroup.Commensurable (verticalLevel α hα n) (baseSubgroup α hα) := by
  rw [verticalLevel_eq_map, baseSubgroup_eq_map]
  -- Mapping both levels through the injective left inclusion preserves their
  -- relative indices; spelling this directly avoids any choice of coset reps.
  constructor
  · rw [Subgroup.relIndex_map_map_of_injective _ _ inl_injective]
    exact (level_commensurable_zero α hα n).1
  ·
    rw [Subgroup.relIndex_map_map_of_injective _ _ inl_injective]
    exact (level_commensurable_zero α hα n).2

/-- Conjugating the vertical base by the stable letter gives exactly the
compressed range. -/
theorem t_conj_base_eq_compressed :
    ConjAct.toConjAct (tVertical α hα) • baseSubgroup α hα =
      ((iotaVertical α hα).comp α).range := by
  ext v
  constructor
  · intro hv
    obtain ⟨b, hb, hbv⟩ :=
      (Subgroup.mem_smul_pointwise_iff_exists v
        (ConjAct.toConjAct (tVertical α hα)) (baseSubgroup α hα)).mp hv
    obtain ⟨γ, rfl⟩ := hb
    refine ⟨γ, ?_⟩
    rw [MonoidHom.comp_apply]
    rw [← vertical_compress α hα]
    simpa [ConjAct.toConjAct_smul] using hbv
  · rintro ⟨γ, rfl⟩
    rw [MonoidHom.comp_apply, ← vertical_compress α hα]
    change ConjAct.toConjAct (tVertical α hα) • iotaVertical α hα γ ∈
      ConjAct.toConjAct (tVertical α hα) • baseSubgroup α hα
    apply Subgroup.smul_mem_pointwise_smul
    exact ⟨γ, rfl⟩

/-- The compressed vertical base has finite index in the base. -/
theorem compressed_commensurable_base [α.range.FiniteIndex] :
    Subgroup.Commensurable ((iotaVertical α hα).comp α).range
      (baseSubgroup α hα) := by
  have hiota : Function.Injective (iotaVertical α hα) :=
    iotaVertical_injective α hα
  have hcompressed : ((iotaVertical α hα).comp α).range =
      α.range.map (iotaVertical α hα) := MonoidHom.range_comp _ _
  rw [hcompressed, baseSubgroup_eq_map_top]
  constructor
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hiota,
      Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  · rw [Subgroup.relIndex_map_map_of_injective _ _ hiota]
    simp

/-- The entire vertical group commensurates its level-zero base. -/
theorem vertical_le_commensurator [α.range.FiniteIndex] :
    (⊤ : Subgroup (Vertical α hα)) ≤
      Subgroup.Commensurable.commensurator (baseSubgroup α hα) := by
  intro v _
  apply vertical_mem_subgroup_of_iota_mem_of_t_mem α hα
      (Subgroup.Commensurable.commensurator (baseSubgroup α hα))
  · intro γ
    rw [Subgroup.Commensurable.commensurator_mem_iff]
    have hnormalizes :
        ConjAct.toConjAct (iotaVertical α hα γ) • baseSubgroup α hα =
          baseSubgroup α hα :=
      Subgroup.conjAct_pointwise_smul_eq_self
        ((baseSubgroup α hα).le_normalizer ⟨γ, rfl⟩)
    rw [hnormalizes]
  · rw [Subgroup.Commensurable.commensurator_mem_iff,
      t_conj_base_eq_compressed]
    exact compressed_commensurable_base α hα

/-- The stabilizer in `L` of the coset represented by `g` is the pullback of
the conjugate of the quotient subgroup. -/
theorem stabilizer_quotient_eq_comap {G : Type*} [Group G]
    (L B : Subgroup G) (g : G) :
    MulAction.stabilizer L (QuotientGroup.mk g : G ⧸ B) =
      (ConjAct.toConjAct g • B).comap L.subtype := by
  ext l
  rw [MulAction.mem_stabilizer_iff]
  change QuotientGroup.mk ((l : G) * g) = QuotientGroup.mk g ↔ _
  rw [QuotientGroup.eq]
  change (((l : G) * g)⁻¹ * g ∈ B) ↔ (l : G) ∈ ConjAct.toConjAct g • B
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [mul_inv_rev, inv_inv, ConjAct.smul_def,
    ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
  constructor
  · intro h
    simpa [mul_assoc] using B.inv_mem h
  · intro h
    simpa [mul_assoc] using B.inv_mem h

/-- A subgroup commensurable with every conjugate of `B` has finite orbits
on `G/B`. -/
theorem finite_orbit_on_quotient_of_commensurated {G : Type*} [Group G]
    (L B : Subgroup G) (hLB : Subgroup.Commensurable L B)
    (hB : (⊤ : Subgroup G) ≤ Subgroup.Commensurable.commensurator B)
    (x : G ⧸ B) :
    (MulAction.orbit L x).Finite := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg := hB (Subgroup.mem_top g)
  rw [Subgroup.Commensurable.commensurator_mem_iff] at hg
  have hLC : Subgroup.Commensurable L (ConjAct.toConjAct g • B) :=
    hLB.trans hg.symm
  have hindex :
      ((ConjAct.toConjAct g • B).comap L.subtype).index ≠ 0 := by
    rw [Subgroup.index_comap, L.range_subtype]
    exact hLC.2
  have hstabilizer :
      MulAction.stabilizer L (QuotientGroup.mk g : G ⧸ B) =
        (ConjAct.toConjAct g • B).comap L.subtype :=
    stabilizer_quotient_eq_comap L B g
  have hstabilizerIndex :
      (MulAction.stabilizer L (QuotientGroup.mk g : G ⧸ B)).index ≠ 0 := by
    rw [hstabilizer]
    exact hindex
  letI : (MulAction.stabilizer L
      (QuotientGroup.mk g : G ⧸ B)).FiniteIndex := ⟨hstabilizerIndex⟩
  rw [← Set.finite_coe_iff]
  exact Finite.of_equiv
    (L ⧸ MulAction.stabilizer L (QuotientGroup.mk g : G ⧸ B))
    (MulAction.orbitEquivQuotientStabilizer L
      (QuotientGroup.mk g : G ⧸ B)).symm

/-- **Finite telescope-level site orbits.** -/
theorem finite_verticalLevel_orbit [α.range.FiniteIndex] (n : ℕ)
    (x : Cosets α hα) :
    (Set.range fun h : verticalLevel α hα n ↦ (h : Vertical α hα) • x).Finite :=
  finite_orbit_on_quotient_of_commensurated
    (verticalLevel α hα n) (baseSubgroup α hα)
    (verticalLevel_commensurable_base α hα n)
    (vertical_le_commensurator α hα) x

end MappingTelescopeFiniteOrbits
end GroupApproximation
