import GroupApproximation.Higman.OmegaTowerStageThree

/-!
# Britton survival for the omega tower

This module begins the hard half of `Omega.TowerClosure`.  It proves the key
case-2 fact: if a row word has a nonzero coefficient in the active window,
then no conjugated second-copy code `g_β` commutes with it in the slim first
stage.
-/

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

variable {G₀ : Type} [Group G₀]

/-- Forget the second centralizing stable letter. -/
def dropCent2 (P : Subgroup G₀) : Cent2 P →* Cent1 P :=
  HNNExtension.lift (MonoidHom.id (Cent1 P)) 1 (by intro z; simp)

@[simp] theorem dropCent2_of (P : Subgroup G₀) (x : Cent1 P) :
    dropCent2 P (of x) = x := by
  simp [dropCent2, HNNExtension.lift_of]

@[simp] theorem dropCent2_t (P : Subgroup G₀) :
    dropCent2 P (t : Cent2 P) = 1 := by
  simp [dropCent2, HNNExtension.lift_t]

/-- Forget the third centralizing stable letter. -/
def dropCent3 (P : Subgroup G₀) : Cent3 P →* Cent2 P :=
  HNNExtension.lift (MonoidHom.id (Cent2 P)) 1 (by intro z; simp)

@[simp] theorem dropCent3_of (P : Subgroup G₀) (x : Cent2 P) :
    dropCent3 P (of x) = x := by
  simp [dropCent3, HNNExtension.lift_of]

@[simp] theorem dropCent3_t (P : Subgroup G₀) :
    dropCent3 P (t : Cent3 P) = 1 := by
  simp [dropCent3, HNNExtension.lift_t]

/-- Retraction of the three-letter first stage to its first HNN layer. -/
def dropToCent1 (P : Subgroup G₀) : Cent3 P →* Cent1 P :=
  (dropCent2 P).comp (dropCent3 P)

@[simp] theorem dropToCent1_emb3 (P : Subgroup G₀) (x : G₀) :
    dropToCent1 P (emb3 P x) = (of x : Cent1 P) := by
  simp [dropToCent1, emb3, emb2, emb1]

@[simp] theorem dropToCent1_gen1 (P : Subgroup G₀) :
    dropToCent1 P (gen1 P) = (t : Cent1 P) := by
  simp [dropToCent1, gen1]

@[simp] theorem dropToCent1_gen2 (P : Subgroup G₀) :
    dropToCent1 P (gen2 P) = 1 := by
  simp [dropToCent1, gen2]

@[simp] theorem dropToCent1_gen3 (P : Subgroup G₀) :
    dropToCent1 P (gen3 P) = 1 := by
  simp [dropToCent1, gen3]

/-- The first-copy projection of the abstract rank-three code. -/
def firstCodeProjection (P : Subgroup G₀) : F₃ →* Cent1 P :=
  FreeGroup.lift fun i : Fin 3 => if i = 0 then (t : Cent1 P) else 1

@[simp] theorem firstCodeProjection_a (P : Subgroup G₀) :
    firstCodeProjection P a = (t : Cent1 P) := by
  simp [firstCodeProjection, a]

@[simp] theorem firstCodeProjection_b (P : Subgroup G₀) :
    firstCodeProjection P b = 1 := by
  simp [firstCodeProjection, b]

@[simp] theorem firstCodeProjection_c (P : Subgroup G₀) :
    firstCodeProjection P c = 1 := by
  simp [firstCodeProjection, c]

theorem dropToCent1_comp_genHom (P : Subgroup G₀) :
    (dropToCent1 P).comp (genHom P) = firstCodeProjection P := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i <;> simp [genHom, firstCodeProjection]

theorem firstCodeProjection_comp_rowHom (P : Subgroup G₀) :
    (firstCodeProjection P).comp rowHom = 1 := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  rw [MonoidHom.comp_apply, rowHom_of]
  unfold rowElt
  simp

@[simp] theorem firstCodeProjection_bElt (P : Subgroup G₀) (β : E) :
    firstCodeProjection P (bElt β) = 1 := by
  unfold bElt
  rw [← MonoidHom.comp_apply, firstCodeProjection_comp_rowHom]
  rfl

@[simp] theorem firstCodeProjection_aElt (P : Subgroup G₀) (β : E) :
    firstCodeProjection P (aElt β) = (t : Cent1 P) := by
  change firstCodeProjection P ((bElt β)⁻¹ * a * bElt β) = _
  rw [map_mul, map_mul, map_inv, firstCodeProjection_bElt,
    firstCodeProjection_a, inv_one, one_mul, mul_one]

@[simp] theorem dropToCent1_genCode (P : Subgroup G₀) (β : E) :
    dropToCent1 P (genHom P (aElt β)) = (t : Cent1 P) := by
  rw [← MonoidHom.comp_apply, dropToCent1_comp_genHom]
  exact firstCodeProjection_aElt P β

/-- Any alleged commutation of `g_β` with a base word descends to the first
stable letter, so Britton forces that base word into the centralized subgroup. -/
theorem genCode_not_commute_of_not_mem (P : Subgroup G₀) (β : E) (x : G₀)
    (hx : x ∉ P) : ¬ Commute (genHom P (aElt β)) (emb3 P x) := by
  intro hcomm
  have hdrop := Commute.map hcomm (dropToCent1 P)
  have ht : Commute (t : Cent1 P) (of x) := by simpa using hdrop
  exact hx ((commute_t_of_iff P x).mp ht)

/-- A coded row word with a nonzero active-window coordinate is not in the
outside associated subgroup. -/
theorem basisHom_elt_not_mem_rowOut {m : ℕ} {l : E} {i : ℤ}
    (hi : i ∈ Finset.Ico (0 : ℤ) (m : ℤ)) (hli : l i ≠ 0) :
    Row.basisHom (elt l) ∉ rowOut m := by
  intro hmem
  have hidx := (basisHom_mem_rowOut_iff m (elt l)).mp hmem
  have hkill := RowDeletionGraph.killOn_eq_self_of_mem_indexSub
    (fun j : ℤ => j ∉ Finset.Ico (0 : ℤ) (m : ℤ)) hidx
  rw [Split.killOn_elt] at hkill
  have hfilt : Finsupp.filter
      (fun j : ℤ => j ∉ Finset.Ico (0 : ℤ) (m : ℤ)) l = l :=
    elt_injective hkill
  have hat := congrArg (fun f : E => f i) hfilt
  have hout : ¬ (i ∉ Finset.Ico (0 : ℤ) (m : ℤ)) := fun h => h hi
  rw [Finsupp.filter_apply, if_neg hout] at hat
  exact hli hat.symm

/-- **Conjugated-code survival.**  If `l` has a nonzero coordinate in the
active window, `g_β` cannot commute with `b_l`. -/
theorem slimGenCode_not_commute_bWord {m : ℕ} (β l : E) {i : ℤ}
    (hi : i ∈ Finset.Ico (0 : ℤ) (m : ℤ)) (hli : l i ≠ 0) :
    ¬ Commute (slimGenCode m β)
      (emb3 (rowOut m) (Row.basisHom (elt l))) := by
  exact genCode_not_commute_of_not_mem (rowOut m) β _
    (basisHom_elt_not_mem_rowOut hi hli)

end Omega
end Higman
end GroupApproximation
