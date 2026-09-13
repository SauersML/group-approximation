import GroupApproximation.TypeA2.Cover
import GroupApproximation.TypeA2.HalfLineOrbits
import GroupApproximation.TypeA2.HalfLineReplica
import GroupApproximation.TypeA2.HalfLineWreath
import GroupApproximation.GroupTheory.HigmanThompson.CompactRangeB

/-!
# The witness for FFWZ Question 5.8

The witness action is a cover `geoF 0 ⋊ FreeGroup (Fin 2)` of geometric Thompson `F`, acting
on the positive dyadic rationals.  The free group acts through replicas: a generator acts on
every interval `[n, n + 1]` as the copy in `compactF 0 1` of the lamp or of the shift of
`HalfLineWreath`.

* `witnessPsi : FreeGroup (Fin 2) →* compactF 0 1` sends the generators to the copies of
  `lampF` and `shiftF`;
* `witnessPhi := replicaHom 0 ∘ witnessPsi` normalizes `geoF 0` and preserves the positive
  dyadics;
* `WitnessGroup` is `geoF 0 ⋊[coverConj (geoF 0) witnessPhi _] FreeGroup (Fin 2)`;
* `WitnessSet` is the set of positive dyadics, with the cover action
  `(γ, h) · x = γ (witnessPhi h x)`.

The prose of this module was written by Claude (Anthropic).
-/

namespace GroupApproximation.TypeA2

open HigmanThompson

/-- `geoF 0` is isomorphic to its copy `compactF 0 1` supported in `[0, 1]`. -/
noncomputable def witnessEquiv : geoF 0 ≃* compactF 0 1 :=
  geoFEquivCompactF 0 1 le_rfl

/-- The free generators go to the copies of the lamp and of the shift. -/
noncomputable def witnessPsi : FreeGroup (Fin 2) →* compactF 0 1 :=
  FreeGroup.lift ![witnessEquiv lampF, witnessEquiv shiftF]

theorem witnessPsi_of_zero : witnessPsi (FreeGroup.of 0) = witnessEquiv lampF :=
  FreeGroup.lift_apply_of

theorem witnessPsi_of_one : witnessPsi (FreeGroup.of 1) = witnessEquiv shiftF :=
  FreeGroup.lift_apply_of

/-- The free group acts on the half line through the replicas of `witnessPsi`. -/
noncomputable def witnessPhi : FreeGroup (Fin 2) →* Equiv.Perm ℚ :=
  (replicaHom 0).comp witnessPsi

theorem witnessPhi_apply (h : FreeGroup (Fin 2)) : witnessPhi h = replica (witnessPsi h).2 :=
  rfl

theorem witnessPhi_mem_normalizer (h : FreeGroup (Fin 2)) :
    witnessPhi h ∈ Subgroup.normalizer (geoF 0 : Set (Equiv.Perm ℚ)) :=
  replica_mem_normalizer (witnessPsi h).2

theorem witnessPhi_mapsTo (h : FreeGroup (Fin 2)) :
    ∀ x ∈ halfLineDyadics, witnessPhi h x ∈ halfLineDyadics :=
  fun _ hx => replica_mapsTo_posGrid (witnessPsi h).2 hx

/-- The acting group of the witness: the cover of `geoF 0` by the free group of rank two. -/
abbrev WitnessGroup : Type :=
  geoF 0 ⋊[coverConj (geoF 0) witnessPhi witnessPhi_mem_normalizer] FreeGroup (Fin 2)

/-- The positive dyadic rationals, with the cover action of `WitnessGroup`. -/
abbrev WitnessSet : Type :=
  coverSubMulAction (geoF 0) witnessPhi witnessPhi_mem_normalizer halfLineDyadics
    (fun _ hg _ hx => geoF_zero_mapsTo hg hx) witnessPhi_mapsTo

theorem one_mem_halfLineDyadics : (1 : ℚ) ∈ halfLineDyadics := by
  show 0 < (1 : ℚ) ∧ ∃ M : ℕ, (1 : ℚ) ∈ Grid 2 M
  refine ⟨one_pos, 0, ?_⟩
  show ∃ k : ℤ, (1 : ℚ) * ((2 : ℕ) : ℚ) ^ 0 = k
  exact ⟨1, by norm_num⟩

instance witnessSet_nonempty : Nonempty WitnessSet :=
  ⟨⟨1, one_mem_halfLineDyadics⟩⟩

end GroupApproximation.TypeA2
