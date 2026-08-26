import GroupApproximation.Higman.OmegaTowerStageThree
import GroupApproximation.Higman.CentralHNNFreeLabelKernel

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
open scoped Pointwise

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

/-! ## Both coordinates of an arbitrary link word -/

/-- Retraction of the first centralizer extension to its original base,
killing the stable letter. -/
def baseRet1 (P : Subgroup G₀) : Cent1 P →* G₀ :=
  HNNExtension.lift (MonoidHom.id G₀) 1 (by intro z; simp)

@[simp] theorem baseRet1_of (P : Subgroup G₀) (x : G₀) :
    baseRet1 P (of x) = x := by
  simp [baseRet1, HNNExtension.lift_of]

@[simp] theorem baseRet1_t (P : Subgroup G₀) :
    baseRet1 P (t : Cent1 P) = 1 := by
  simp [baseRet1, HNNExtension.lift_t]

/-- Retraction through the second centralizer extension. -/
def baseRet2 (P : Subgroup G₀) : Cent2 P →* G₀ :=
  HNNExtension.lift (baseRet1 P) 1 (by
    intro z
    change 1 * baseRet1 P z = baseRet1 P z * 1
    simp)

@[simp] theorem baseRet2_of (P : Subgroup G₀) (x : Cent1 P) :
    baseRet2 P (of x) = baseRet1 P x := by
  simp [baseRet2, HNNExtension.lift_of]

@[simp] theorem baseRet2_t (P : Subgroup G₀) :
    baseRet2 P (t : Cent2 P) = 1 := by
  simp [baseRet2, HNNExtension.lift_t]

/-- Retraction of the full three-letter first stage to the original base. -/
def baseRet3 (P : Subgroup G₀) : Cent3 P →* G₀ :=
  HNNExtension.lift (baseRet2 P) 1 (by
    intro z
    change 1 * baseRet2 P z = baseRet2 P z * 1
    simp)

@[simp] theorem baseRet3_of (P : Subgroup G₀) (x : Cent2 P) :
    baseRet3 P (of x) = baseRet2 P x := by
  simp [baseRet3, HNNExtension.lift_of]

@[simp] theorem baseRet3_t (P : Subgroup G₀) :
    baseRet3 P (t : Cent3 P) = 1 := by
  simp [baseRet3, HNNExtension.lift_t]

@[simp] theorem baseRet3_emb3 (P : Subgroup G₀) (x : G₀) :
    baseRet3 P (emb3 P x) = x := by
  simp [emb3, emb2, emb1]

@[simp] theorem baseRet3_gen1 (P : Subgroup G₀) :
    baseRet3 P (gen1 P) = 1 := by
  simp [gen1]

@[simp] theorem baseRet3_gen2 (P : Subgroup G₀) :
    baseRet3 P (gen2 P) = 1 := by
  simp [gen2]

@[simp] theorem baseRet3_gen3 (P : Subgroup G₀) :
    baseRet3 P (gen3 P) = 1 := by
  simp [gen3]

theorem baseRet3_comp_genHom (P : Subgroup G₀) :
    (baseRet3 P).comp (genHom P) = 1 := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i <;> simp [genHom]

/-- The row-coordinate word paired with a word in window blocks. -/
noncomputable def blockRowHom (m : ℕ) :
    FreeGroup ↥(blockSet m) →* Row.F₀ :=
  FreeGroup.lift fun β => Row.basisHom (elt β.1)

/-- The same block alphabet with every generator inverted.  This is a
homomorphism (unlike inversion of an arbitrary noncommutative word). -/
noncomputable def blockRowInvHom (m : ℕ) :
    FreeGroup ↥(blockSet m) →* Row.F₀ :=
  FreeGroup.lift fun β => (Row.basisHom (elt β.1))⁻¹

/-- The base retraction reads an arbitrary link word as the inverse of its
paired row word. -/
theorem baseRet3_comp_slimLinkLift (m : ℕ) :
    (baseRet3 (rowOut m)).comp (slimLinkLift m) =
      blockRowInvHom m := by
  refine FreeGroup.ext_hom _ _ fun β => ?_
  simp only [MonoidHom.comp_apply, slimLinkLift, FreeGroup.lift_apply_of,
    slimLinkElem, map_mul, map_inv, slimGenCode, slimBaseCode,
    blockRowInvHom]
  rw [← MonoidHom.comp_apply, baseRet3_comp_genHom,
    baseRet3_emb3]
  simp

/-- The subgroup of the first stage generated by the selected second-copy
block codes. -/
noncomputable def slimGenSub (m : ℕ) (B : Set E) :
    Subgroup (Cent3 (rowOut m)) :=
  Subgroup.closure (slimGenCode m '' (B ∩ blockSet m))

/-- The second-copy embedding is injective, detected by `genProjection3`. -/
theorem genHom_injective (m : ℕ) :
    Function.Injective (genHom (rowOut m)) := by
  intro x y hxy
  have h := congrArg (genProjection3 m) hxy
  rwa [← MonoidHom.comp_apply, ← MonoidHom.comp_apply,
    genProjection3_comp_genHom, MonoidHom.id_apply, MonoidHom.id_apply] at h

/-- The selected first-stage `g`-subgroup is literally the image of the
corresponding conjugate subgroup of `F₃`. -/
theorem slimGenSub_eq_map_ASub (m : ℕ) (B : Set E) :
    slimGenSub m B =
      (ASub (B ∩ blockSet m)).map (genHom (rowOut m)) := by
  unfold slimGenSub ASub slimGenCode
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨aElt β, ⟨β, hβ, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨β, hβ, rfl⟩, rfl⟩
    exact ⟨β, hβ, rfl⟩

@[simp] theorem genProjection3_slimGenCode (m : ℕ) (β : E) :
    genProjection3 m (slimGenCode m β) = aElt β := by
  unfold slimGenCode
  rw [← MonoidHom.comp_apply, genProjection3_comp_genHom]
  rfl

/-- The code projection of every selected `g`-word lies in `A_B`. -/
theorem genProjection3_mem_ASub_of_mem_slimGenSub {m : ℕ} {B : Set E}
    {z : Cent3 (rowOut m)} (hz : z ∈ slimGenSub m B) :
    genProjection3 m z ∈ ASub B := by
  unfold slimGenSub at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      rw [genProjection3_slimGenCode]
      exact Subgroup.subset_closure ⟨β, hβ.1, rfl⟩
  | one => simp
  | mul x y hx hy ihx ihy => simpa only [map_mul] using Subgroup.mul_mem _ ihx ihy
  | inv x hx ih => simpa only [map_inv] using Subgroup.inv_mem _ ih

/-- The row retraction kills every selected `g`-word. -/
theorem baseRet3_eq_one_of_mem_slimGenSub {m : ℕ} {B : Set E}
    {z : Cent3 (rowOut m)} (hz : z ∈ slimGenSub m B) :
    baseRet3 (rowOut m) z = 1 := by
  unfold slimGenSub at hz
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨β, hβ, rfl⟩ := hx
      unfold slimGenCode
      rw [← MonoidHom.comp_apply, baseRet3_comp_genHom]
      rfl
  | one => simp
  | mul x y hx hy ihx ihy => simp [map_mul, ihx, ihy]
  | inv x hx ih => simp [map_inv, ih]

/-- **Arbitrary stage-two pinch classification.**  If a selected `g`-word
also lies in the link subgroup, it has a link spelling whose code coordinate
lies in `A_B` and whose row coordinate is trivial.  This replaces the
generator-only calculation by the exact invariant preserved by every pinch
collapse. -/
theorem exists_link_word_of_mem_slimGenSub {m : ℕ} {B : Set E}
    {z : Cent3 (rowOut m)} (hzG : z ∈ slimGenSub m B)
    (hzL : z ∈ slimLink m) :
    ∃ w : FreeGroup ↥(blockSet m), slimLinkLift m w = z ∧
      blockAHom m w ∈ ASub B ∧ blockRowInvHom m w = 1 := by
  rw [← slimLinkLift_range m] at hzL
  obtain ⟨w, rfl⟩ := hzL
  refine ⟨w, rfl, ?_, ?_⟩
  · rw [← genProjection3_comp_slimLinkLift m, MonoidHom.comp_apply]
    exact genProjection3_mem_ASub_of_mem_slimGenSub hzG
  · rw [← baseRet3_comp_slimLinkLift m, MonoidHom.comp_apply]
    exact baseRet3_eq_one_of_mem_slimGenSub hzG

/-! ## The outer Britton spelling

The last HNN stage does not introduce any new base generators into `W`.
The subgroup below is therefore the exact stage-two alphabet seen by an
outer normal-form scan. -/

/-- The stage-two subgroup generated by `a` and the selected second-copy
block codes. -/
noncomputable def slimWBase (m : ℕ) (B : Set E) : Subgroup (SlimPi m) :=
  Subgroup.closure
    ({slimPiF3Hom m a} ∪
      (fun β : E => slimPiOf m (slimGenCode m β)) '' (B ∩ blockSet m))

/-- Every subgroup of the base is stable for a central HNN extension: the
edge equivalence is the identity. -/
theorem stable_refl_slimGenSub (m : ℕ) (B : Set E) :
    HNNDescent.Stable (MulEquiv.refl (slimLink m)) (slimGenSub m B) := by
  constructor <;> intro z hz <;> exact hz

/-- The stage-two alphabet is exactly `⟨slimGenSub, a⟩` in the central HNN
extension. -/
theorem slimWBase_eq_innerClosure (m : ℕ) (B : Set E) :
    slimWBase m B =
      Subgroup.closure
        (HNNDescent.genSet (MulEquiv.refl (slimLink m)) (slimGenSub m B)) := by
  apply le_antisymm
  · rw [slimWBase, Subgroup.closure_le]
    rintro x (hx | hx)
    · rw [Set.mem_singleton_iff] at hx
      subst x
      apply Subgroup.subset_closure
      exact Set.mem_union_right _ rfl
    · obtain ⟨β, hβ, rfl⟩ := hx
      apply Subgroup.subset_closure
      left
      refine ⟨slimGenCode m β, ?_, rfl⟩
      exact Subgroup.subset_closure ⟨β, hβ, rfl⟩
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨z, hz, rfl⟩ := hx
      induction hz using Subgroup.closure_induction with
      | mem y hy =>
          obtain ⟨β, hβ, rfl⟩ := hy
          exact Subgroup.subset_closure
            (Set.mem_union_right _ ⟨β, hβ, rfl⟩)
      | one => simp
      | mul x y hx hy ihx ihy =>
          change slimPiOf m (x * y) ∈ slimWBase m B
          rw [map_mul]
          exact Subgroup.mul_mem _ ihx ihy
      | inv x hx ih =>
          change slimPiOf m x⁻¹ ∈ slimWBase m B
          rw [map_inv]
          exact Subgroup.inv_mem _ ih
    · rw [Set.mem_singleton_iff] at hx
      subst x
      exact Subgroup.subset_closure (Set.mem_union_left _ rfl)

/-- **The inner Britton descent.**  The stage-two subgroup generated by `a`
and the selected `g`-codes meets the first-stage base in exactly the selected
`g`-subgroup. -/
theorem slimWBase_inf_innerRange (m : ℕ) (B : Set E) :
    slimWBase m B ⊓ (slimPiOf m).range =
      (slimGenSub m B).map (slimPiOf m) := by
  rw [slimWBase_eq_innerClosure]
  exact HNNDescent.closure_inf_range (MulEquiv.refl (slimLink m))
    (stable_refl_slimGenSub m B)

/-- Elementwise form of the inner descent, used at every outer pinch. -/
theorem mem_slimGenSub_of_of_mem_slimWBase {m : ℕ} {B : Set E}
    {z : Cent3 (rowOut m)} (hz : slimPiOf m z ∈ slimWBase m B) :
    z ∈ slimGenSub m B := by
  rw [slimWBase_eq_innerClosure] at hz
  exact HNNDescent.mem_of_of_mem_closure (MulEquiv.refl (slimLink m))
    (stable_refl_slimGenSub m B) hz

/-- Retraction of the slim second stage to its first-stage base, killing the
second stable letter `a`. -/
noncomputable def slimPiBaseRet (m : ℕ) : SlimPi m →* Cent3 (rowOut m) :=
  HNNExtension.lift (MonoidHom.id (Cent3 (rowOut m))) 1 (by intro z; simp)

@[simp] theorem slimPiBaseRet_of (m : ℕ) (z : Cent3 (rowOut m)) :
    slimPiBaseRet m (slimPiOf m z) = z := by
  simp [slimPiBaseRet, slimPiOf, HNNExtension.lift_of]

@[simp] theorem slimPiBaseRet_t (m : ℕ) :
    slimPiBaseRet m (t : SlimPi m) = 1 := by
  simp [slimPiBaseRet, HNNExtension.lift_t]

/-- Killing the second stable letter sends the stage-two alphabet back into
the selected `g`-subgroup. -/
theorem slimPiBaseRet_mem_slimGenSub_of_mem_slimWBase {m : ℕ} {B : Set E}
    {x : SlimPi m} (hx : x ∈ slimWBase m B) :
    slimPiBaseRet m x ∈ slimGenSub m B := by
  unfold slimWBase at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · rw [Set.mem_singleton_iff] at hx
        subst x
        simp
      · obtain ⟨β, hβ, rfl⟩ := hx
        rw [slimPiBaseRet_of]
        exact Subgroup.subset_closure ⟨β, hβ, rfl⟩
  | one => simp
  | mul x y hx hy ihx ihy => simpa only [map_mul] using Subgroup.mul_mem _ ihx ihy
  | inv x hx ih => simpa only [map_inv] using Subgroup.inv_mem _ ih

/-- `genProjection3` is faithful on the selected `g`-subgroup. -/
theorem eq_one_of_mem_slimGenSub_of_genProjection3_eq_one {m : ℕ} {B : Set E}
    {z : Cent3 (rowOut m)} (hz : z ∈ slimGenSub m B)
    (hproj : genProjection3 m z = 1) : z = 1 := by
  have hrange : z ∈ (genHom (rowOut m)).range := by
    clear hproj
    unfold slimGenSub at hz
    induction hz using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨β, hβ, rfl⟩ := hx
        exact ⟨aElt β, rfl⟩
    | one => exact ⟨1, map_one _⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨u, rfl⟩ := ihx
        obtain ⟨v, rfl⟩ := ihy
        exact ⟨u * v, map_mul _ _ _⟩
    | inv x hx ih =>
        obtain ⟨u, rfl⟩ := ih
        exact ⟨u⁻¹, map_inv _ _⟩
  obtain ⟨u, rfl⟩ := hrange
  have hu : u = 1 := by
    have h := hproj
    rw [← MonoidHom.comp_apply, genProjection3_comp_genHom] at h
    simpa using h
  rw [hu, map_one]

/-- The code projection kills the retained row part of the embedded `F₃`. -/
theorem genProjection3_slimPiBaseRet_comp_slimPiF3Hom (m : ℕ) :
    (genProjection3 m).comp ((slimPiBaseRet m).comp (slimPiF3Hom m)) = 1 := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i <;>
    simp [MonoidHom.comp_apply, slimPiF3Hom, slimPiRowEmb]

/-- Reading the retained row word back in `F₃` agrees with the standard
retraction `retK` that kills `a`. -/
theorem rowIntoF3_baseRet3_slimPiBaseRet_comp_slimPiF3Hom (m : ℕ) :
    rowIntoF3.comp ((baseRet3 (rowOut m)).comp
      ((slimPiBaseRet m).comp (slimPiF3Hom m))) = Coord.retK := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i <;>
    simp [MonoidHom.comp_apply, slimPiF3Hom, slimPiRowEmb, Coord.retK]

/-- **No stray row content survives the inner scan.**  Every embedded `F₃`
word belonging to the stage-two alphabet lies in the kernel of `retK`, hence
in the normal closure of `a`. -/
theorem retK_eq_one_of_slimPiF3Hom_mem_slimWBase {m : ℕ} {B : Set E}
    {x : F₃} (hx : slimPiF3Hom m x ∈ slimWBase m B) : Coord.retK x = 1 := by
  let z : Cent3 (rowOut m) := slimPiBaseRet m (slimPiF3Hom m x)
  have hzG : z ∈ slimGenSub m B :=
    slimPiBaseRet_mem_slimGenSub_of_mem_slimWBase hx
  have hproj : genProjection3 m z = 1 := by
    change ((genProjection3 m).comp
      ((slimPiBaseRet m).comp (slimPiF3Hom m))) x = 1
    rw [genProjection3_slimPiBaseRet_comp_slimPiF3Hom]
    rfl
  have hz : z = 1 :=
    eq_one_of_mem_slimGenSub_of_genProjection3_eq_one hzG hproj
  have hrow : baseRet3 (rowOut m) z = 1 := by rw [hz, map_one]
  rw [← rowIntoF3_baseRet3_slimPiBaseRet_comp_slimPiF3Hom m,
    MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]
  rw [hrow, map_one]

/-- The kernel of the retraction killing `a` is exactly the free subgroup on
all conjugates `a^k`, `k ∈ K`. -/
theorem ker_retK_eq_cbHom_range :
    MonoidHom.ker Coord.retK = Conj.cbHom.range := by
  have hS : ({1} : Set F₃) ⊆ (Conj.K : Set F₃) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact Subgroup.one_mem _
  have hsup : Coord.Aset ({1} : Set F₃) ⊔ Conj.K = ⊤ := by
    apply top_unique
    rw [← FreeGroup.closure_range_of (Fin 3)]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨i, rfl⟩
    fin_cases i
    · change a ∈ Coord.Aset ({1} : Set F₃) ⊔ Conj.K
      apply Subgroup.mem_sup_left
      have ha : Coord.conjA 1 = a := by simp [Coord.conjA]
      rw [← ha]
      exact Coord.conjA_mem_Aset rfl
    · change b ∈ Coord.Aset ({1} : Set F₃) ⊔ Conj.K
      exact Subgroup.mem_sup_right Conj.b_mem_K
    · change c ∈ Coord.Aset ({1} : Set F₃) ⊔ Conj.K
      exact Subgroup.mem_sup_right Conj.c_mem_K
  have hprod : ({1} : Set F₃) * (Conj.K : Set F₃) = (Conj.K : Set F₃) := by
    ext x
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      rw [Set.mem_singleton_iff] at hu
      subst u
      simpa using hv
    · intro hx
      exact ⟨1, rfl, x, hx, one_mul x⟩
  have hker := Coord.Aset_mul_subgroup hS (show Conj.K ≤ Conj.K from le_rfl)
  rw [hsup, top_inf_eq, hprod] at hker
  rw [hker, Coord.Aset_eq_map (show (Conj.K : Set F₃) ⊆ Conj.K from fun _ h => h)]
  have htoK : Coord.toK (Conj.K : Set F₃) = Set.univ := by
    ext x
    simp [Coord.toK]
  rw [htoK, Set.image_univ, FreeGroup.closure_range_of]
  apply le_antisymm
  · rintro x ⟨w, hw, rfl⟩
    exact ⟨w, rfl⟩
  · rintro x ⟨w, rfl⟩
    exact ⟨w, Subgroup.mem_top w, rfl⟩

/-- Every inner survivor has a unique word in the conjugate basis. -/
theorem exists_cbWord_of_slimPiF3Hom_mem_slimWBase {m : ℕ} {B : Set E}
    {x : F₃} (hx : slimPiF3Hom m x ∈ slimWBase m B) :
    ∃ w : FreeGroup ↥Conj.K, Conj.cbHom w = x := by
  have hker : x ∈ MonoidHom.ker Coord.retK :=
    MonoidHom.mem_ker.mpr (retK_eq_one_of_slimPiF3Hom_mem_slimWBase hx)
  rw [ker_retK_eq_cbHom_range] at hker
  obtain ⟨w, hw⟩ := hker
  exact ⟨w, hw⟩

/-! ## The exact free coordinates of the inner matched spelling -/

/-- A fixed right-coset transversal for the central second stage. -/
noncomputable def slimTransversal (m : ℕ) :
    HNNExtension.NormalWord.TransversalPair
      (Cent3 (rowOut m)) (slimLink m) (slimLink m) :=
  Classical.choice inferInstance

/-- The generic base retraction is the concrete retraction already used by
the slim tower. -/
theorem slimPiBaseRet_eq_freeLabelBaseRet (m : ℕ) :
    slimPiBaseRet m =
      CentralHNNFreeLabel.baseRet (slimLink m) := rfl

/-- Concrete coordinate form of the inner matched spelling. -/
theorem slimWBase_inf_baseRet_ker (m : ℕ) (B : Set E) :
    slimWBase m B ⊓ (slimPiBaseRet m).ker =
      (CentralHNNFreeLabel.labelSub (slimLink m) (slimTransversal m)
        (slimGenSub m B)).map
          (CentralHNNFreeLabel.stableConjLift
            (slimLink m) (slimTransversal m)) := by
  rw [slimWBase_eq_innerClosure, slimPiBaseRet_eq_freeLabelBaseRet]
  exact CentralHNNFreeLabel.closure_inf_ker_baseRet
    (slimLink m) (slimTransversal m) (slimGenSub m B)

/-- On the subgroup `K = ⟨b,c⟩`, the row retraction followed by the standard
rank-two inclusion is the identity. -/
theorem rowIntoF3_retract_coe_K (q : ↥Conj.K) :
    rowIntoF3 (Seq.retract (q : F₃)) = (q : F₃) := by
  have hall : ∀ (y : F₃) (hy : y ∈ Conj.K),
      rowIntoF3 (Seq.retract y) = y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with rfl | hy
        · simp
        · rw [Set.mem_singleton_iff] at hy
          subst y
          simp
    | one => simp
    | mul x y hx hy ihx ihy => simp [map_mul, ihx, ihy]
    | inv x hx ih => simp [map_inv, ih]
  exact hall q q.property

/-- The conjugating subgroup `K` inside the first-stage base. -/
noncomputable def slimKBase (m : ℕ) : ↥Conj.K →* Cent3 (rowOut m) :=
  (emb3 (rowOut m)).comp (Seq.retract.comp Conj.K.subtype)

theorem slimPiF3Hom_comp_rowIntoF3 (m : ℕ) :
    (slimPiF3Hom m).comp rowIntoF3 = slimPiRowEmb m := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · change slimPiF3Hom m b = slimPiRowEmb m Row.b
    exact slimPiF3Hom_b m
  · change slimPiF3Hom m c = slimPiRowEmb m Row.c
    exact slimPiF3Hom_c m

/-- The stage-two copy of an element of `K` is the base element read through
the row retraction. -/
theorem slimPiF3Hom_coe_K (m : ℕ) (q : ↥Conj.K) :
    slimPiF3Hom m (q : F₃) = slimPiOf m (slimKBase m q) := by
  calc
    slimPiF3Hom m (q : F₃) =
        slimPiF3Hom m (rowIntoF3 (Seq.retract (q : F₃))) := by
      rw [rowIntoF3_retract_coe_K]
    _ = slimPiRowEmb m (Seq.retract (q : F₃)) := by
      rw [← MonoidHom.comp_apply, slimPiF3Hom_comp_rowIntoF3]
    _ = slimPiOf m (slimKBase m q) := rfl

/-- Replace each conjugating word in `K` by its right-coset label modulo the
link subgroup. -/
noncomputable def slimLabelHom (m : ℕ) :
    FreeGroup ↥Conj.K →*
      FreeGroup (CentralHNNFreeLabel.Label
        (slimLink m) (slimTransversal m)) :=
  FreeGroup.map fun q : ↥Conj.K =>
    (((slimTransversal m).compl (1 : ℤˣ)).equiv (slimKBase m q)).2

/-- **Matched conjugates have exactly the same free coset spelling.** -/
theorem slimPiF3Hom_comp_cbHom_eq_freeLabel (m : ℕ) :
    (slimPiF3Hom m).comp Conj.cbHom =
      (CentralHNNFreeLabel.stableConjLift
        (slimLink m) (slimTransversal m)).comp (slimLabelHom m) := by
  refine FreeGroup.ext_hom _ _ fun q => ?_
  simp only [MonoidHom.comp_apply, Conj.cbHom_of, map_mul, map_inv,
    slimPiF3Hom_coe_K, slimPiF3Hom_a, slimLabelHom, FreeGroup.map.of,
    CentralHNNFreeLabel.stableConjLift, FreeGroup.lift_apply_of]
  exact (CentralHNNFreeLabel.stableConj_eq_conj_of_label_eq
    (slimLink m) (slimTransversal m)
    (((slimTransversal m).compl (1 : ℤˣ)).equiv (slimKBase m q)).2
    (slimKBase m q) rfl).symm

/-- Distinct elements of the row subgroup have distinct right-coset labels:
the row base meets the link subgroup trivially. -/
theorem slimLabelIndex_injective (m : ℕ) : Function.Injective
    (fun q : ↥Conj.K =>
      (((slimTransversal m).compl (1 : ℤˣ)).equiv (slimKBase m q)).2) := by
  intro q r hqr
  have hmem : slimKBase m q * (slimKBase m r)⁻¹ ∈ slimLink m := by
    apply (FiniteHNNFreeLabelAction.source_transversal_eq_iff
      (A := slimLink m) (B := slimLink m) (slimTransversal m)
      (slimKBase m q * (slimKBase m r)⁻¹) (slimKBase m r)).1
    simpa [mul_assoc] using hqr
  have hrow : Seq.retract (q : F₃) * (Seq.retract (r : F₃))⁻¹ = 1 := by
    have hc : Seq.retract (q : F₃) * (Seq.retract (r : F₃))⁻¹ ∈
        (slimLink m).comap (emb3 (rowOut m)) := by
      simpa [slimKBase, map_mul, map_inv] using hmem
    rw [slimLink_comap_emb3_eq_bot, Subgroup.mem_bot] at hc
    exact hc
  apply Subtype.ext
  rw [← rowIntoF3_retract_coe_K q, ← rowIntoF3_retract_coe_K r]
  exact congrArg rowIntoF3 (mul_inv_eq_one.mp hrow)

/-- The row-to-coset spelling loses no free information. -/
theorem slimLabelHom_injective (m : ℕ) :
    Function.Injective (slimLabelHom m) :=
  FreeGroup.map_injective (slimLabelIndex_injective m)

/-- **Every inner survivor has a literal word supported on the cosets met by
the selected second-copy subgroup.** -/
theorem slimLabelHom_mem_of_cbHom_survives {m : ℕ} {B : Set E}
    {w : FreeGroup ↥Conj.K}
    (hw : slimPiF3Hom m (Conj.cbHom w) ∈ slimWBase m B) :
    slimLabelHom m w ∈
      CentralHNNFreeLabel.labelSub (slimLink m) (slimTransversal m)
        (slimGenSub m B) := by
  let lift := CentralHNNFreeLabel.stableConjLift
    (slimLink m) (slimTransversal m)
  have heq : slimPiF3Hom m (Conj.cbHom w) = lift (slimLabelHom m w) := by
    exact DFunLike.congr_fun (slimPiF3Hom_comp_cbHom_eq_freeLabel m) w
  have hker : slimPiF3Hom m (Conj.cbHom w) ∈ (slimPiBaseRet m).ker := by
    change slimPiBaseRet m (slimPiF3Hom m (Conj.cbHom w)) = 1
    rw [heq, slimPiBaseRet_eq_freeLabelBaseRet,
      ← MonoidHom.comp_apply, CentralHNNFreeLabel.baseRet_comp_stableConjLift]
    rfl
  have hinter : slimPiF3Hom m (Conj.cbHom w) ∈
      slimWBase m B ⊓ (slimPiBaseRet m).ker := ⟨hw, hker⟩
  rw [slimWBase_inf_baseRet_ker] at hinter
  obtain ⟨v, hv, hvz⟩ := hinter
  have hvw : v = slimLabelHom m w :=
    CentralHNNFreeLabel.stableConjLift_injective
      (slimLink m) (slimTransversal m) (hvz.trans heq)
  rwa [hvw] at hv

/-- The row indices whose link coset meets the selected second-copy subgroup. -/
def slimMatchedK (m : ℕ) (B : Set E) : Set ↥Conj.K :=
  (fun q : ↥Conj.K =>
    (((slimTransversal m).compl (1 : ℤˣ)).equiv (slimKBase m q)).2) ⁻¹'
      CentralHNNFreeLabel.labelSet (slimLink m) (slimTransversal m)
        (slimGenSub m B)

/-- Reflect the selected coset support all the way back to the original free
word on `K`. -/
theorem mem_closure_slimMatchedK_of_cbHom_survives {m : ℕ} {B : Set E}
    {w : FreeGroup ↥Conj.K}
    (hw : slimPiF3Hom m (Conj.cbHom w) ∈ slimWBase m B) :
    w ∈ Subgroup.closure (FreeGroup.of '' slimMatchedK m B) := by
  apply CentralHNNFreeLabel.Coordinate.mem_closure_preimage_of_map_mem
    (slimLabelIndex_injective m)
  exact slimLabelHom_mem_of_cbHom_survives hw

/-- A matched row coset has a link spelling whose two projections are the
selected second-copy word and the inverse row word, respectively. -/
theorem exists_link_word_of_mem_slimMatchedK {m : ℕ} {B : Set E}
    {q : ↥Conj.K} (hq : q ∈ slimMatchedK m B) :
    ∃ (s : Cent3 (rowOut m)) (u : FreeGroup ↥(blockSet m)),
      s ∈ slimGenSub m B ∧
      slimLinkLift m u = s * (slimKBase m q)⁻¹ ∧
      blockAHom m u ∈ ASub B ∧
      blockRowInvHom m u = (Seq.retract (q : F₃))⁻¹ := by
  obtain ⟨s, hs, hlabel⟩ := hq
  have hlink : s * (slimKBase m q)⁻¹ ∈ slimLink m := by
    apply (FiniteHNNFreeLabelAction.source_transversal_eq_iff
      (A := slimLink m) (B := slimLink m) (slimTransversal m)
      (s * (slimKBase m q)⁻¹) (slimKBase m q)).1
    simpa [mul_assoc] using hlabel
  rw [← slimLinkLift_range m] at hlink
  obtain ⟨u, hu⟩ := hlink
  refine ⟨s, u, hs, hu, ?_, ?_⟩
  · have hsA := genProjection3_mem_ASub_of_mem_slimGenSub hs
    rw [← genProjection3_comp_slimLinkLift m, MonoidHom.comp_apply, hu,
      map_mul, map_inv]
    simpa [slimKBase] using hsA
  · rw [← baseRet3_comp_slimLinkLift m, MonoidHom.comp_apply, hu,
      map_mul, map_inv, baseRet3_eq_one_of_mem_slimGenSub hs]
    simp [slimKBase]

/-- The block alphabet restricted to the selected set `B`. -/
def selectedBlocks (m : ℕ) (B : Set E) : Set ↥(blockSet m) :=
  {β | (β : E) ∈ B}

/-- Reflect a selected `A_B` value of the block basis map back to the literal
selected block letters. -/
theorem mem_closure_selectedBlocks_of_blockAHom_mem {m : ℕ} {B : Set E}
    {u : FreeGroup ↥(blockSet m)} (hu : blockAHom m u ∈ ASub B) :
    u ∈ Subgroup.closure (FreeGroup.of '' selectedBlocks m B) := by
  have himage : FreeGroup.map (blockToK m) u ∈
      Subgroup.closure (FreeGroup.of '' (bK '' B)) := by
    rw [ASub_eq_map] at hu
    obtain ⟨v, hv, hvu⟩ := hu
    have heq : Conj.cbHom (FreeGroup.map (blockToK m) u) = Conj.cbHom v := by
      have hvu' := hvu
      rw [blockAHom_eq, MonoidHom.comp_apply] at hvu'
      exact hvu'.symm
    have := Conj.cbHom_injective heq
    rwa [this]
  have hreflect :=
    CentralHNNFreeLabel.Coordinate.mem_closure_preimage_of_map_mem
      (blockToK_injective m) (bK '' B) himage
  have hpre : (blockToK m ⁻¹' (bK '' B)) = selectedBlocks m B := by
    ext β
    constructor
    · rintro ⟨f, hf, hfb⟩
      have hbβ : blockToK m β = bK (β : E) := Subtype.ext rfl
      rw [hbβ] at hfb
      have : (β : E) = f := bK_injective hfb.symm
      simpa [selectedBlocks, this] using hf
    · intro hβ
      exact ⟨(β : E), hβ, rfl⟩
  rwa [hpre] at hreflect

/-- The inverse row word carried by a block spelling, as an element of `K`. -/
noncomputable def blockKInvHom (m : ℕ) :
    FreeGroup ↥(blockSet m) →* ↥Conj.K :=
  FreeGroup.lift fun β => (blockToK m β)⁻¹

theorem rowIntoF3_comp_basisHom :
    rowIntoF3.comp Row.basisHom = rowHom := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  simp only [MonoidHom.comp_apply, Row.basisHom_of, rowHom_of]
  unfold Row.row rowElt
  rw [map_mul, map_mul, map_zpow, map_zpow, rowIntoF3_b, rowIntoF3_c]

/-- The `K`-valued inverse block word has the same underlying row value as
`blockRowInvHom`. -/
theorem Ksubtype_comp_blockKInvHom (m : ℕ) :
    Conj.K.subtype.comp (blockKInvHom m) =
      rowIntoF3.comp (blockRowInvHom m) := by
  refine FreeGroup.ext_hom _ _ fun β => ?_
  simp only [MonoidHom.comp_apply, blockKInvHom, FreeGroup.lift_apply_of,
    map_inv, blockRowInvHom]
  congr 1
  change ((blockToK m β : ↥Conj.K) : F₃) =
    rowIntoF3 (Row.basisHom (elt (β : E)))
  rw [← MonoidHom.comp_apply, rowIntoF3_comp_basisHom]
  rfl

/-- The local row subgroup generated by the selected window blocks. -/
noncomputable def localKSub (m : ℕ) (B : Set E) : Subgroup ↥Conj.K :=
  Subgroup.closure (bK '' (B ∩ blockSet m))

/-- **Every matched row coset belongs to the subgroup generated by selected
window blocks.** -/
theorem mem_localKSub_of_mem_slimMatchedK {m : ℕ} {B : Set E}
    {q : ↥Conj.K} (hq : q ∈ slimMatchedK m B) : q ∈ localKSub m B := by
  obtain ⟨s, u, hs, hu, hAu, hrow⟩ :=
    exists_link_word_of_mem_slimMatchedK hq
  have huB : u ∈ Subgroup.closure (FreeGroup.of '' selectedBlocks m B) :=
    mem_closure_selectedBlocks_of_blockAHom_mem hAu
  have hmap : ∀ {v : FreeGroup ↥(blockSet m)},
      v ∈ Subgroup.closure (FreeGroup.of '' selectedBlocks m B) →
      blockKInvHom m v ∈ localKSub m B := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨β, hβ, rfl⟩ := hx
        rw [blockKInvHom, FreeGroup.lift_apply_of]
        apply Subgroup.inv_mem
        exact Subgroup.subset_closure
          ⟨(β : E), ⟨hβ, β.property⟩, rfl⟩
    | one => simp
    | mul x y hx hy ihx ihy => simpa only [map_mul] using Subgroup.mul_mem _ ihx ihy
    | inv x hx ih => simpa only [map_inv] using Subgroup.inv_mem _ ih
  have hK : blockKInvHom m u ∈ localKSub m B := hmap huB
  have heq : blockKInvHom m u = q⁻¹ := by
    apply Subtype.ext
    have hmap := congrArg rowIntoF3 hrow
    rw [← MonoidHom.comp_apply, ← Ksubtype_comp_blockKInvHom m,
      MonoidHom.comp_apply] at hmap
    simpa [map_inv, rowIntoF3_retract_coe_K] using hmap
  have := (localKSub m B).inv_mem hK
  rwa [heq, inv_inv] at this

/-- The free coordinate subgroup indexed by the local selected-block row
subgroup. -/
noncomputable def localCoordSub (m : ℕ) (B : Set E) :
    Subgroup (FreeGroup ↥Conj.K) :=
  Subgroup.closure (FreeGroup.of '' (localKSub m B : Set ↥Conj.K))

/-- An inner survivor is supported on local selected-block row words. -/
theorem mem_localCoordSub_of_cbHom_survives {m : ℕ} {B : Set E}
    {w : FreeGroup ↥Conj.K}
    (hw : slimPiF3Hom m (Conj.cbHom w) ∈ slimWBase m B) :
    w ∈ localCoordSub m B := by
  apply (Subgroup.closure_mono (Set.image_mono ?_))
    (mem_closure_slimMatchedK_of_cbHom_survives hw)
  intro q hq
  exact mem_localKSub_of_mem_slimMatchedK hq

/-- **Complete inner-pinch classifier.**  Every `F₃` element whose stage-two
copy lies in `slimWBase` has a conjugate-basis spelling supported on the local
selected-block row subgroup. -/
theorem exists_local_cbWord_of_slimPiF3Hom_mem_slimWBase
    {m : ℕ} {B : Set E} {x : F₃}
    (hx : slimPiF3Hom m x ∈ slimWBase m B) :
    ∃ w : FreeGroup ↥Conj.K,
      w ∈ localCoordSub m B ∧ Conj.cbHom w = x := by
  obtain ⟨w, hw⟩ := exists_cbWord_of_slimPiF3Hom_mem_slimWBase hx
  refine ⟨w, ?_, hw⟩
  apply mem_localCoordSub_of_cbHom_survives
  rwa [hw]

/-! ## The one-letter obstruction in the first stage -/

/-- **A bad window cannot acquire a row coset through one selected code.**
If `l` has a nonzero active-window coordinate, then the right coset of
`b_l g_β` modulo the link subgroup contains no element of the row copy.

This is the exact case-2 obstruction used by the outer Britton scan.  If such
a row representative existed, faithfulness of `genProjection3` on the link
would identify the alleged link element with `g_β b_β⁻¹`.  After
rearranging and forgetting the last two centralizing letters, one obtains a
first-stage pinch `t⁻¹ b_l t` in the row base.  Britton then puts `b_l` in
`rowOut`, contradicting the active coordinate. -/
theorem slimBase_mul_gen_mul_rowInv_not_mem_slimLink
    {m : ℕ} {β l : E} (hβ : β ∈ blockSet m) {i : ℤ}
    (hi : i ∈ Finset.Ico (0 : ℤ) (m : ℤ)) (hli : l i ≠ 0)
    (q : ↥Conj.K) :
    slimBaseCode m l * slimGenCode m β * (slimKBase m q)⁻¹ ∉ slimLink m := by
  intro hlink
  have hcanonical : slimLinkElem m β ∈ slimLink m :=
    slimLinkElem_mem hβ
  have hproj : genProjection3 m
        (slimBaseCode m l * slimGenCode m β * (slimKBase m q)⁻¹) =
      genProjection3 m (slimLinkElem m β) := by
    simp [slimBaseCode, slimKBase, slimLinkElem]
  have heq : slimBaseCode m l * slimGenCode m β * (slimKBase m q)⁻¹ =
      slimLinkElem m β :=
    genProjection3_injOn_slimLink m hlink hcanonical hproj
  have hconj :
      (slimGenCode m β)⁻¹ * slimBaseCode m l * slimGenCode m β =
        (slimBaseCode m β)⁻¹ * slimKBase m q := by
    unfold slimLinkElem at heq
    calc
      (slimGenCode m β)⁻¹ * slimBaseCode m l * slimGenCode m β =
          (slimGenCode m β)⁻¹ *
            (slimBaseCode m l * slimGenCode m β * (slimKBase m q)⁻¹) *
              slimKBase m q := by group
      _ = (slimGenCode m β)⁻¹ *
            (slimGenCode m β * (slimBaseCode m β)⁻¹) *
              slimKBase m q := by rw [heq]
      _ = (slimBaseCode m β)⁻¹ * slimKBase m q := by group
  have hdrop := congrArg (dropToCent1 (rowOut m)) hconj
  have hbase :
      (t : Cent1 (rowOut m))⁻¹ *
          of (Row.basisHom (elt l)) * (t : Cent1 (rowOut m)) ∈
        (of : Row.F₀ →* Cent1 (rowOut m)).range := by
    refine ⟨(Row.basisHom (elt β))⁻¹ * Seq.retract (q : F₃), ?_⟩
    simpa [slimBaseCode, slimKBase, slimGenCode, map_mul, map_inv,
      dropToCent1_genCode] using hdrop.symm
  exact basisHom_elt_not_mem_rowOut hi hli
    (mem_of_conj_mem_range (rowOut m) hbase)

/-- The right-coset label of a row conjugator in the central second stage. -/
noncomputable def slimRowLabel (m : ℕ) (q : ↥Conj.K) :
    CentralHNNFreeLabel.Label (slimLink m) (slimTransversal m) :=
  (((slimTransversal m).compl (1 : ℤˣ)).equiv (slimKBase m q)).2

/-- The right-coset label read by the conjugator `b_l g_β`. -/
noncomputable def slimCodeLabel (m : ℕ) (l β : E) :
    CentralHNNFreeLabel.Label (slimLink m) (slimTransversal m) :=
  (((slimTransversal m).compl (1 : ℤˣ)).equiv
    (slimBaseCode m l * slimGenCode m β)).2

/-- A bad active-window conjugator has a coset label outside the entire row
label range. -/
theorem slimCodeLabel_not_mem_rowLabel_range
    {m : ℕ} {β l : E} (hβ : β ∈ blockSet m) {i : ℤ}
    (hi : i ∈ Finset.Ico (0 : ℤ) (m : ℤ)) (hli : l i ≠ 0) :
    slimCodeLabel m l β ∉ Set.range (slimRowLabel m) := by
  rintro ⟨q, hq⟩
  apply slimBase_mul_gen_mul_rowInv_not_mem_slimLink hβ hi hli q
  apply (FiniteHNNFreeLabelAction.source_transversal_eq_iff
    (A := slimLink m) (B := slimLink m) (slimTransversal m)
    (slimBaseCode m l * slimGenCode m β * (slimKBase m q)⁻¹)
    (slimKBase m q)).1
  simpa [slimCodeLabel, slimRowLabel, mul_assoc] using hq.symm

/-- The stage-two conjugate by `g_β` is the free stable conjugate indexed by
the coset of `b_l g_β`. -/
theorem slimGen_conj_aElt_eq_stableConj
    (m : ℕ) (l β : E) :
    (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
        slimPiOf m (slimGenCode m β) =
      CentralHNNFreeLabel.stableConj (slimLink m) (slimTransversal m)
        (slimCodeLabel m l β) := by
  rw [CentralHNNFreeLabel.stableConj_eq_conj_of_label_eq
    (slimLink m) (slimTransversal m) (slimCodeLabel m l β)
    (slimBaseCode m l * slimGenCode m β) rfl]
  unfold aElt
  rw [map_mul, map_mul, map_inv, slimPiF3Hom_bElt, slimPiF3Hom_a,
    map_mul, map_inv]
  rw [show (of (slimBaseCode m l * slimGenCode m β) : SlimPi m) =
      slimPiOf m (slimBaseCode m l) * slimPiOf m (slimGenCode m β) by
    exact map_mul (slimPiOf m) _ _]
  rfl

/-- **Case-2 survival at the second stage.**  Conjugating `a_l` by a selected
`g_β` cannot return to the embedded `F₃` when `l` has a nonzero coordinate
in the active window. -/
theorem slimGen_conj_aElt_not_mem_F3Range
    {m : ℕ} {β l : E} (hβ : β ∈ blockSet m) {i : ℤ}
    (hi : i ∈ Finset.Ico (0 : ℤ) (m : ℤ)) (hli : l i ≠ 0) :
    (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
        slimPiOf m (slimGenCode m β) ∉ (slimPiF3Hom m).range := by
  rintro ⟨x, hx⟩
  have hbase : slimPiBaseRet m (slimPiF3Hom m x) = 1 := by
    rw [hx, slimGen_conj_aElt_eq_stableConj]
    exact CentralHNNFreeLabel.baseRet_stableConj
      (slimLink m) (slimTransversal m) (slimCodeLabel m l β)
  have hret : Coord.retK x = 1 := by
    rw [← rowIntoF3_baseRet3_slimPiBaseRet_comp_slimPiF3Hom m,
      MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
      hbase, map_one, map_one]
  have hxker : x ∈ MonoidHom.ker Coord.retK := MonoidHom.mem_ker.mpr hret
  rw [ker_retK_eq_cbHom_range] at hxker
  obtain ⟨w, hw⟩ := hxker
  let lift := CentralHNNFreeLabel.stableConjLift
    (slimLink m) (slimTransversal m)
  have hlift : lift (FreeGroup.of (slimCodeLabel m l β)) =
      lift (slimLabelHom m w) := by
    calc
      lift (FreeGroup.of (slimCodeLabel m l β)) =
          CentralHNNFreeLabel.stableConj (slimLink m) (slimTransversal m)
            (slimCodeLabel m l β) := by
              simp [lift, CentralHNNFreeLabel.stableConjLift]
      _ = (slimPiOf m (slimGenCode m β))⁻¹ *
          slimPiF3Hom m (aElt l) * slimPiOf m (slimGenCode m β) :=
            (slimGen_conj_aElt_eq_stableConj m l β).symm
      _ = slimPiF3Hom m x := hx.symm
      _ = slimPiF3Hom m (Conj.cbHom w) := by rw [hw]
      _ = lift (slimLabelHom m w) :=
        DFunLike.congr_fun (slimPiF3Hom_comp_cbHom_eq_freeLabel m) w
  have hword : FreeGroup.of (slimCodeLabel m l β) = slimLabelHom m w :=
    CentralHNNFreeLabel.stableConjLift_injective
      (slimLink m) (slimTransversal m) hlift
  have hsupport : FreeGroup.of (slimCodeLabel m l β) ∈
      Subgroup.closure (FreeGroup.of '' Set.range (slimRowLabel m)) := by
    rw [hword]
    change FreeGroup.map (slimRowLabel m) w ∈
      Subgroup.closure (FreeGroup.of '' Set.range (slimRowLabel m))
    exact CentralHNNFreeLabel.Coordinate.map_mem_closure_range
      (slimRowLabel m) w
  exact slimCodeLabel_not_mem_rowLabel_range hβ hi hli
    (CentralHNNFreeLabel.Coordinate.index_mem_of_of_mem_closure hsupport)

/-- **Case-1 collapse at the second stage.**  If `l` is supported outside the
active window, then `g_β` commutes past its row code, so conjugating `a_l` by
`g_β` simply inserts the selected block conjugate `a_β`. -/
theorem slimGen_conj_aElt_eq_rowConj_of_outside
    {m : ℕ} {β l : E} (hβ : β ∈ blockSet m)
    (hl : ∀ i : ℤ, l i ≠ 0 → i ∉ Finset.Ico (0 : ℤ) (m : ℤ)) :
    (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
        slimPiOf m (slimGenCode m β) =
      (slimPiF3Hom m (bElt l))⁻¹ * slimPiF3Hom m (aElt β) *
        slimPiF3Hom m (bElt l) := by
  have htop := commute_gen_bElt (slimTower m) hβ hl
  have hcomm : Commute
      (slimPiOf m (slimGenCode m β))
      (slimPiF3Hom m (bElt l)) := by
    change Commute
      (slimOmegaOf m (slimPiOf m (slimGenCode m β)))
      (slimOmegaOf m (slimPiF3Hom m (bElt l))) at htop
    have hmul : slimOmegaOf m
          (slimPiOf m (slimGenCode m β) * slimPiF3Hom m (bElt l)) =
        slimOmegaOf m
          (slimPiF3Hom m (bElt l) * slimPiOf m (slimGenCode m β)) := by
      rw [map_mul, map_mul]
      exact htop.eq
    exact HNNExtension.of_injective (slimShiftRangeEquiv m) hmul
  calc
    (slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
          slimPiOf m (slimGenCode m β) =
        (slimPiF3Hom m (bElt l))⁻¹ *
          ((slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m a *
            slimPiOf m (slimGenCode m β)) *
          slimPiF3Hom m (bElt l) := by
      unfold aElt
      rw [map_mul, map_mul, map_inv]
      exact conj_swap hcomm.symm
    _ = (slimPiF3Hom m (bElt l))⁻¹ * slimPiF3Hom m (aElt β) *
          slimPiF3Hom m (bElt l) := by
      rw [slim_conj_gen m β hβ]

/-- The two one-letter cases form an exact seam test: the conjugated code
returns to the embedded `F₃` exactly when its row conjugator is supported
outside the active window. -/
theorem slimGen_conj_aElt_mem_F3Range_iff
    {m : ℕ} {β l : E} (hβ : β ∈ blockSet m) :
    ((slimPiOf m (slimGenCode m β))⁻¹ * slimPiF3Hom m (aElt l) *
        slimPiOf m (slimGenCode m β) ∈ (slimPiF3Hom m).range) ↔
      ∀ i : ℤ, l i ≠ 0 → i ∉ Finset.Ico (0 : ℤ) (m : ℤ) := by
  constructor
  · intro hmem i hli hi
    exact slimGen_conj_aElt_not_mem_F3Range hβ hi hli hmem
  · intro hout
    refine ⟨(bElt l)⁻¹ * aElt β * bElt l, ?_⟩
    rw [map_mul, map_mul, map_inv]
    exact (slimGen_conj_aElt_eq_rowConj_of_outside hβ hout).symm

/-- Every element of the concrete `W` lies in the standard outer-HNN
subgroup generated by the stage-two alphabet and the final stable letter.
This is the bridge from subgroup membership to `HNNDescent`'s word scan. -/
theorem slimW_le_outerClosure (m : ℕ) (B : Set E) :
    W (slimTower m) B ≤
      Subgroup.closure
        (HNNDescent.genSet (slimShiftRangeEquiv m) (slimWBase m B)) := by
  rw [W, Subgroup.closure_le]
  rintro x (hx | hx)
  · rcases hx with rfl | rfl
    · apply Subgroup.subset_closure
      left
      refine ⟨slimPiF3Hom m a, ?_, rfl⟩
      exact Subgroup.subset_closure (Set.mem_union_left _ rfl)
    · have ht : (HNNExtension.t : SlimOmega m) ∈
          Subgroup.closure
            (HNNDescent.genSet (slimShiftRangeEquiv m) (slimWBase m B)) :=
        Subgroup.subset_closure (Set.mem_union_right _ rfl)
      change (HNNExtension.t : SlimOmega m)⁻¹ ∈
        Subgroup.closure
          (HNNDescent.genSet (slimShiftRangeEquiv m) (slimWBase m B))
      exact Subgroup.inv_mem _ ht
  · obtain ⟨β, hβ, rfl⟩ := hx
    apply Subgroup.subset_closure
    left
    refine ⟨slimPiOf m (slimGenCode m β), ?_, rfl⟩
    exact Subgroup.subset_closure
      (Set.mem_union_right _ ⟨β, hβ, rfl⟩)

/-- **Outer spelling for `W`.**  Every element of `W` is a Britton word for
the final HNN extension, and every base entry of that word lies in
`slimWBase`. -/
theorem exists_outer_gword_of_mem_slimW {m : ℕ} {B : Set E} {x : SlimOmega m}
    (hx : x ∈ W (slimTower m) B) :
    ∃ (z₀ : SlimPi m) (l : List (ℤˣ × SlimPi m)),
      z₀ ∈ slimWBase m B ∧ (∀ p ∈ l, p.2 ∈ slimWBase m B) ∧
        x = HNNDescent.gword (slimShiftRangeEquiv m) z₀ l :=
  HNNDescent.exists_gword (slimShiftRangeEquiv m)
    (slimW_le_outerClosure m B hx)

end Omega
end Higman
end GroupApproximation
