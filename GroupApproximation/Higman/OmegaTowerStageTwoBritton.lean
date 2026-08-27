import GroupApproximation.Algebra.HNNSubextension
import GroupApproximation.Algebra.HNNTrivialAssociated
import GroupApproximation.Algebra.HNNRetraction
import GroupApproximation.Computability.FreeByRetraction
import GroupApproximation.Higman.OmegaTowerStageTwo

namespace GroupApproximation
namespace Higman
namespace Omega

open GroupApproximation.Higman.Conj
open GroupApproximation.Higman.Seq
open HNNExtension

/-! ## The projection that detects the link subgroup -/

def genProjection1 (m : ℕ) : Cent1 (rowOut m) →* F₃ :=
  HNNExtension.lift 1 a (by intro z; simp)

@[simp] theorem genProjection1_of (m : ℕ) (x : Row.F₀) :
    genProjection1 m (emb1 (rowOut m) x) = 1 := by
  simp [genProjection1, emb1, HNNExtension.lift_of]

@[simp] theorem genProjection1_t (m : ℕ) :
    genProjection1 m (t : Cent1 (rowOut m)) = a := by
  simp [genProjection1, HNNExtension.lift_t]

def genProjection2 (m : ℕ) : Cent2 (rowOut m) →* F₃ :=
  HNNExtension.lift (genProjection1 m) b (by
    intro z
    obtain ⟨x, hx, hxz⟩ := z.property
    have hz : genProjection1 m (z : Cent1 (rowOut m)) = 1 := by
      rw [← hxz]
      exact genProjection1_of m x
    change b * genProjection1 m z = genProjection1 m z * b
    rw [hz, mul_one, one_mul])

@[simp] theorem genProjection2_of (m : ℕ) (x : Cent1 (rowOut m)) :
    genProjection2 m (of x) = genProjection1 m x := by
  simp [genProjection2, HNNExtension.lift_of]

@[simp] theorem genProjection2_t (m : ℕ) :
    genProjection2 m (t : Cent2 (rowOut m)) = b := by
  simp [genProjection2, HNNExtension.lift_t]

def genProjection3 (m : ℕ) : Cent3 (rowOut m) →* F₃ :=
  HNNExtension.lift (genProjection2 m) c (by
    intro z
    obtain ⟨x, hx, hxz⟩ := z.property
    have hz : genProjection2 m (z : Cent2 (rowOut m)) = 1 := by
      rw [← hxz]
      rw [genProjection2_of]
      obtain ⟨y, hy, hyx⟩ := hx
      rw [← hyx]
      exact genProjection1_of m y
    change c * genProjection2 m z = genProjection2 m z * c
    rw [hz, mul_one, one_mul])

@[simp] theorem genProjection3_of (m : ℕ) (x : Cent2 (rowOut m)) :
    genProjection3 m (of x) = genProjection2 m x := by
  simp [genProjection3, HNNExtension.lift_of]

@[simp] theorem genProjection3_t (m : ℕ) :
    genProjection3 m (t : Cent3 (rowOut m)) = c := by
  simp [genProjection3, HNNExtension.lift_t]

@[simp] theorem genProjection3_emb3 (m : ℕ) (x : Row.F₀) :
    genProjection3 m (emb3 (rowOut m) x) = 1 := by
  change genProjection1 m (emb1 (rowOut m) x) = 1
  exact genProjection1_of m x

theorem genProjection3_comp_genHom (m : ℕ) :
    (genProjection3 m).comp (genHom (rowOut m)) = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i <;> simp [genHom, gen1, gen2, gen3, a, b, c]

/-! ## The link is free and detected by the projection -/

noncomputable def blockToK (m : ℕ) (β : ↥(blockSet m)) : ↥Conj.K :=
  ⟨bElt β.1, bElt_mem_K β.1⟩

theorem blockToK_injective (m : ℕ) : Function.Injective (blockToK m) := by
  intro β γ h
  apply Subtype.ext
  exact bElt_injective (congrArg Subtype.val h)

noncomputable def blockAHom (m : ℕ) : FreeGroup ↥(blockSet m) →* F₃ :=
  FreeGroup.lift fun β => aElt β.1

theorem blockAHom_eq (m : ℕ) :
    blockAHom m = Conj.cbHom.comp (FreeGroup.map (blockToK m)) := by
  refine FreeGroup.ext_hom _ _ fun β => ?_
  simp [blockAHom, blockToK, aElt_eq_cbHom]

theorem blockAHom_injective (m : ℕ) : Function.Injective (blockAHom m) := by
  rw [blockAHom_eq]
  exact Conj.cbHom_injective.comp
    (FreeGroup.map_injective (blockToK_injective m))

noncomputable def slimLinkLift (m : ℕ) :
    FreeGroup ↥(blockSet m) →* Cent3 (rowOut m) :=
  FreeGroup.lift fun β => slimLinkElem m β.1

theorem genProjection3_comp_slimLinkLift (m : ℕ) :
    (genProjection3 m).comp (slimLinkLift m) = blockAHom m := by
  refine FreeGroup.ext_hom _ _ fun β => ?_
  rw [MonoidHom.comp_apply]
  simp only [slimLinkLift, FreeGroup.lift_apply_of]
  unfold slimLinkElem slimGenCode slimBaseCode blockAHom
  rw [map_mul, map_inv, ← MonoidHom.comp_apply, genProjection3_comp_genHom,
    MonoidHom.id_apply, genProjection3_emb3, inv_one, mul_one,
    FreeGroup.lift_apply_of]

theorem slimLinkLift_injective (m : ℕ) : Function.Injective (slimLinkLift m) := by
  intro x y hxy
  apply blockAHom_injective m
  rw [← genProjection3_comp_slimLinkLift m]
  exact congrArg (genProjection3 m) hxy

theorem slimLinkLift_range (m : ℕ) : (slimLinkLift m).range = slimLink m := by
  unfold slimLinkLift
  rw [FreeByRetraction.range_lift_eq_closure]
  unfold slimLink
  congr 1
  ext x
  constructor
  · rintro ⟨β, rfl⟩
    exact ⟨β.1, β.2, rfl⟩
  · rintro ⟨β, hβ, rfl⟩
    exact ⟨⟨β, hβ⟩, rfl⟩

theorem genProjection3_injOn_slimLink (m : ℕ) :
    Set.InjOn (genProjection3 m) (slimLink m) := by
  intro x hx y hy hxy
  rw [← slimLinkLift_range m] at hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  apply congrArg (slimLinkLift m)
  apply blockAHom_injective m
  rw [← genProjection3_comp_slimLinkLift m,
    MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact hxy

/-- The row carrier meets the stage-two associated subgroup trivially. -/
theorem slimLink_comap_emb3_eq_bot (m : ℕ) :
    (slimLink m).comap (emb3 (rowOut m)) = ⊥ := by
  ext x
  simp only [Subgroup.mem_comap, Subgroup.mem_bot]
  constructor
  · intro hx
    have hone : (1 : Cent3 (rowOut m)) ∈ slimLink m := Subgroup.one_mem _
    have hproj : genProjection3 m (emb3 (rowOut m) x) =
        genProjection3 m (1 : Cent3 (rowOut m)) := by simp
    have hbase : emb3 (rowOut m) x = 1 :=
      genProjection3_injOn_slimLink m hx hone hproj
    exact emb3_injective (rowOut m) (by simpa using hbase)
  · rintro rfl
    simp

/-! ## Britton subextension and the rank-three embedding -/

theorem rowIsSubextension (m : ℕ) : HNNSubextension.IsSubextension
    (MulEquiv.refl (slimLink m)) (MulEquiv.refl (⊥ : Subgroup Row.F₀))
    (emb3 (rowOut m)) where
  inj := emb3_injective _
  memA z := by
    have hz : (z : Row.F₀) = 1 := Subgroup.mem_bot.mp z.property
    rw [hz, map_one]
    exact Subgroup.one_mem _
  satA x hx := by
    rw [← Subgroup.mem_comap, slimLink_comap_emb3_eq_bot] at hx
    exact hx
  satB x hx := by
    rw [← Subgroup.mem_comap, slimLink_comap_emb3_eq_bot] at hx
    exact hx
  compat z hz := by simp

abbrev RowFreeHNN : Type := HNNTrivialAssociated.FreeProd Row.F₀

def rowIntoF3 : Row.F₀ →* F₃ :=
  FreeGroup.map fun i : Fin 2 => (⟨i + 1, by omega⟩ : Fin 3)

@[simp] theorem rowIntoF3_b : rowIntoF3 Row.b = b := by
  simp [rowIntoF3, Row.b, b]

@[simp] theorem rowIntoF3_c : rowIntoF3 Row.c = c := by
  simp [rowIntoF3, Row.c, c]

def rowFreeHNNToF3 : RowFreeHNN →* F₃ :=
  HNNExtension.lift rowIntoF3 a (by
    intro z
    have hz : (z : Row.F₀) = 1 := Subgroup.mem_bot.mp z.property
    simp [hz])

def f3ToRowFreeHNN : F₃ →* RowFreeHNN :=
  FreeGroup.lift fun i : Fin 3 =>
    if i = 0 then (t : RowFreeHNN)
    else if i = 1 then of Row.b
    else of Row.c

theorem f3ToRowFreeHNN_injective : Function.Injective f3ToRowFreeHNN := by
  have hcomp : rowFreeHNNToF3.comp f3ToRowFreeHNN = MonoidHom.id F₃ := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    fin_cases i <;>
      simp [rowFreeHNNToF3, f3ToRowFreeHNN, a, b, c,
        HNNExtension.lift_t, HNNExtension.lift_of]
  intro x y hxy
  have := congrArg rowFreeHNNToF3 hxy
  rwa [← MonoidHom.comp_apply, ← MonoidHom.comp_apply, hcomp] at this

noncomputable def rowCanonical (m : ℕ) : RowFreeHNN →* SlimPi m :=
  HNNSubextension.canonical (rowIsSubextension m)

theorem rowCanonical_injective (m : ℕ) : Function.Injective (rowCanonical m) :=
  HNNSubextension.injective_of_isSubextensionHom (rowIsSubextension m)
    (HNNSubextension.isSubextensionHom_canonical (rowIsSubextension m))

theorem slimPiF3Hom_eq (m : ℕ) :
    slimPiF3Hom m = (rowCanonical m).comp f3ToRowFreeHNN := by
  have hcan := HNNSubextension.isSubextensionHom_canonical (rowIsSubextension m)
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · change (t : SlimPi m) = rowCanonical m (t : RowFreeHNN)
    exact hcan.map_t.symm
  · change of (emb3 (rowOut m) Row.b) = rowCanonical m (of Row.b)
    exact (hcan.map_of Row.b).symm
  · change of (emb3 (rowOut m) Row.c) = rowCanonical m (of Row.c)
    exact (hcan.map_of Row.c).symm

/-- **The missing stage-two Britton lemma.** -/
theorem slimPiF3Hom_injective (m : ℕ) : Function.Injective (slimPiF3Hom m) := by
  rw [slimPiF3Hom_eq]
  exact (rowCanonical_injective m).comp f3ToRowFreeHNN_injective

end Omega
end Higman
end GroupApproximation
