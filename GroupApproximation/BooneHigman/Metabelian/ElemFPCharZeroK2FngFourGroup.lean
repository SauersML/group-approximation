import GroupApproximation.BooneHigman.Metabelian.ElemFPCharZeroK2FngGen
import GroupApproximation.GroupTheory.FGAbelianFinitePresentation
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Subgroup.Centralizer
import GroupApproximation.Meta.AxiomGuard

/-!
# Kernels normally generated modulo a subgroup with commutative image

Lane `bh-met-92p`, group-theory helper module.  Nothing here is about Steinberg groups.

* `czK2FngFour_ker_subgroupOf_closure`: for `f : G →* W` and a finite `T ⊆ G` whose images
  pairwise commute, `ker f ∩ ⟨T⟩` is finitely normally generated **in `⟨T⟩`**.  Proof: `⟨T⟩` is
  finitely generated and maps onto `⟨f '' T⟩`, which is commutative and finitely generated,
  hence finitely presented (`isFinitelyPresented_of_commGroup`); Tietze with a finitely generated
  source (`czK2Fng_ker_of_fg`) does the rest.
* `czK2FngFour_fng_of_le_sup`: (Dedekind modular law) if `K ⊴ G`, `S ⊆ K` is finite,
  `K ∩ C` is finitely normally generated in `C`, and `K ≤ ⟪S⟫ ⊔ C`, then `K` is finitely
  normally generated in `G`.  Write `x ∈ K` as `y z` with `y ∈ ⟪S⟫ ≤ K`, `z ∈ C`; then
  `z ∈ K ∩ C`, which lies in the normal closure of the image of its finite normal generators.
* `czK2FngFour_ker_fng_of_le_sup_closure`: the two combined.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero

/-- **Commutative-image Tietze.**  If the images of a finite set `T` pairwise commute, then
`ker f ∩ ⟨T⟩` is finitely normally generated in `⟨T⟩`. -/
theorem czK2FngFour_ker_subgroupOf_closure {G W : Type*} [Group G] [Group W] (f : G →* W)
    (T : Set G) (hT : T.Finite) (hcomm : ∀ x ∈ T, ∀ y ∈ T, f x * f y = f y * f x) :
    (f.ker.subgroupOf (Subgroup.closure T)).IsFinitelyNormallyGenerated := by
  haveI : Finite T := hT.to_subtype
  have hmem : ∀ c : Subgroup.closure T,
      (f.comp (Subgroup.closure T).subtype) c ∈ Subgroup.closure (f '' T) := by
    intro c
    rw [← MonoidHom.map_closure]
    exact Subgroup.mem_map_of_mem f c.2
  let g : Subgroup.closure T →* Subgroup.closure (f '' T) :=
    (f.comp (Subgroup.closure T).subtype).codRestrict (Subgroup.closure (f '' T)) hmem
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (Subgroup.closure T).map f := by
      rw [MonoidHom.map_closure]
      exact hy
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hy'
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  have hfgW : Group.FG (Subgroup.closure (f '' T)) := Group.fg_of_surjective hg
  haveI hcW : IsMulCommutative (Subgroup.closure (f '' T)) := by
    apply Subgroup.isMulCommutative_closure
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact hcomm x hx y hy
  haveI hfp : Group.IsFinitelyPresented (Subgroup.closure (f '' T)) :=
    @GroupApproximation.FGAbelianFinitePresentation.isFinitelyPresented_of_commGroup
      (Subgroup.closure (f '' T))
      { (inferInstance : Group (Subgroup.closure (f '' T))) with
        mul_comm := fun a b ↦ mul_comm' a b } hfgW
  have hker : g.ker = f.ker.subgroupOf (Subgroup.closure T) := by
    show ((f.comp (Subgroup.closure T).subtype).codRestrict
      (Subgroup.closure (f '' T)) hmem).ker = f.ker.subgroupOf (Subgroup.closure T)
    rw [MonoidHom.ker_codRestrict]
    exact (MonoidHom.comap_ker f (Subgroup.closure T).subtype).symm
  rw [← hker]
  exact czK2Fng_ker_of_fg g hg

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngFour_ker_subgroupOf_closure

/-- **Dedekind step.**  A normal subgroup contained in `⟪S⟫ ⊔ C` (with `S ⊆ K` finite) is
finitely normally generated as soon as `K ∩ C` is finitely normally generated in `C`. -/
theorem czK2FngFour_fng_of_le_sup {G : Type*} [Group G] (K C : Subgroup G) [K.Normal]
    (S : Set G) (hS : S.Finite) (hSK : S ⊆ K)
    (hC : (K.subgroupOf C).IsFinitelyNormallyGenerated)
    (hle : K ≤ Subgroup.normalClosure S ⊔ C) :
    K.IsFinitelyNormallyGenerated := by
  obtain ⟨U, hU, hUC⟩ := hC
  refine ⟨S ∪ C.subtype '' U, hS.union (hU.image _), le_antisymm ?_ ?_⟩
  · apply Subgroup.normalClosure_le_normal
    rintro _ (hx | ⟨u, hu, rfl⟩)
    · exact hSK hx
    · have hu' : u ∈ K.subgroupOf C := by
        rw [← hUC]
        exact Subgroup.subset_normalClosure hu
      exact Subgroup.mem_subgroupOf.mp hu'
  · intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := Subgroup.normalClosure S) (t := C)).mp (hle hx)
    have hyK : y ∈ K := Subgroup.normalClosure_le_normal hSK hy
    have hzK : z ∈ K := by
      have h1 := K.mul_mem (K.inv_mem hyK) hx
      rwa [inv_mul_cancel_left] at h1
    have hzC : (⟨z, hz⟩ : C) ∈ K.subgroupOf C := Subgroup.mem_subgroupOf.mpr hzK
    rw [← hUC] at hzC
    have hz' : z ∈ Subgroup.normalClosure (C.subtype '' U) :=
      Subgroup.map_normalClosure_le U C.subtype (Subgroup.mem_map_of_mem C.subtype hzC)
    rw [Subgroup.normalClosure_union]
    exact Subgroup.mul_mem_sup hy hz'

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngFour_fng_of_le_sup

/-- **Combined.**  `ker f ≤ ⟪S⟫ ⊔ ⟨T⟩` with `S ⊆ ker f` finite and `T` finite with pairwise
commuting images gives `ker f` finitely normally generated. -/
theorem czK2FngFour_ker_fng_of_le_sup_closure {G W : Type*} [Group G] [Group W] (f : G →* W)
    (S T : Set G) (hS : S.Finite) (hSK : S ⊆ f.ker) (hT : T.Finite)
    (hcomm : ∀ x ∈ T, ∀ y ∈ T, f x * f y = f y * f x)
    (hle : f.ker ≤ Subgroup.normalClosure S ⊔ Subgroup.closure T) :
    f.ker.IsFinitelyNormallyGenerated :=
  czK2FngFour_fng_of_le_sup f.ker (Subgroup.closure T) S hS hSK
    (czK2FngFour_ker_subgroupOf_closure f T hT hcomm) hle

#audit_axioms
  GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero.czK2FngFour_ker_fng_of_le_sup_closure

end GroupApproximation.BooneHigman.Metabelian.ElemFPCharZero
