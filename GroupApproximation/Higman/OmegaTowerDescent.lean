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
