import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Group
import GroupApproximation.Algebra.ProductFinitePresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Finitely generated abelian groups are finitely presented

Hyde–Lodha's casing lemma (their Lemma 4.2) uses that a subgroup of a finitely generated abelian
group has the finiteness property in question.  For finite presentation:

* `subgroup_fg_of_commGroup`: subgroups of finitely generated commutative groups are finitely
  generated (`ℤ` is noetherian);
* `isFinitelyPresented_of_commGroup`: a finitely generated commutative group is finitely presented.
  On a finite generating set `S`, the kernel of `F(S) ↠ G` contains the finitely many commutators of
  generators; modulo them `F(S)` is commutative and finitely generated, so the image of the kernel is
  finitely generated, and lifts of its generators together with the commutators normally generate
  the kernel;
* `isFinitelyPresented_subgroup_of_commGroup`.
-/

namespace GroupApproximation
namespace FGAbelianFinitePresentation

open scoped commutatorElement

/-- **Subgroups of finitely generated commutative groups are finitely generated.** -/
theorem subgroup_fg_of_commGroup {G : Type*} [CommGroup G] [Group.FG G] (H : Subgroup G) :
    H.FG := by
  haveI : Module.Finite ℤ (Additive G) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  have h1 : (AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup H)).FG :=
    IsNoetherian.noetherian _
  rw [Submodule.fg_iff_addSubgroup_fg, AddSubgroup.toIntSubmodule_toAddSubgroup] at h1
  exact (Subgroup.fg_iff_add_fg H).mpr h1

/-- **Finitely generated commutative groups are finitely presented.** -/
theorem isFinitelyPresented_of_commGroup (G : Type*) [CommGroup G] [Group.FG G] :
    Group.IsFinitelyPresented G := by
  obtain ⟨S, hS, hSfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  haveI : Finite S := Set.finite_coe_iff.mpr hSfin
  let φ : FreeGroup S →* G := FreeGroup.lift (Subtype.val : S → G)
  have hφ : Function.Surjective φ := by
    intro g
    have hle : Subgroup.closure S ≤ φ.range := by
      rw [Subgroup.closure_le]
      intro s hs
      exact ⟨FreeGroup.of ⟨s, hs⟩, FreeGroup.lift_apply_of⟩
    exact hle (by rw [hS]; exact Subgroup.mem_top g)
  let R₁ : Set (FreeGroup S) :=
    Set.range (fun p : S × S => ⁅FreeGroup.of p.1, FreeGroup.of p.2⁆)
  let C : Subgroup (FreeGroup S) := Subgroup.normalClosure R₁
  haveI hCn : C.Normal := Subgroup.normalClosure_normal
  have hgen : ∀ s t : S, QuotientGroup.mk' C (FreeGroup.of s) * QuotientGroup.mk' C (FreeGroup.of t) =
      QuotientGroup.mk' C (FreeGroup.of t) * QuotientGroup.mk' C (FreeGroup.of s) := by
    intro s t
    have h : QuotientGroup.mk' C ⁅FreeGroup.of s, FreeGroup.of t⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨(s, t), rfl⟩)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at h
    exact h.eq
  have hclosure : ∀ x : FreeGroup S ⧸ C,
      x ∈ Subgroup.closure (Set.range fun s : S => QuotientGroup.mk' C (FreeGroup.of s)) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective C x
    have hle : Subgroup.closure (Set.range (FreeGroup.of : S → FreeGroup S)) ≤
        (Subgroup.closure (Set.range fun s : S => QuotientGroup.mk' C (FreeGroup.of s))).comap
          (QuotientGroup.mk' C) := by
      rw [Subgroup.closure_le]
      rintro _ ⟨s, rfl⟩
      exact Subgroup.subset_closure ⟨s, rfl⟩
    have hy : y ∈ Subgroup.closure (Set.range (FreeGroup.of : S → FreeGroup S)) := by
      rw [FreeGroup.closure_range_of]
      exact Subgroup.mem_top y
    exact hle hy
  have hcentral : ∀ s : S, ∀ x : FreeGroup S ⧸ C,
      QuotientGroup.mk' C (FreeGroup.of s) * x = x * QuotientGroup.mk' C (FreeGroup.of s) := by
    intro s x
    have hle : Subgroup.closure (Set.range fun t : S => QuotientGroup.mk' C (FreeGroup.of t)) ≤
        Subgroup.centralizer {QuotientGroup.mk' C (FreeGroup.of s)} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨t, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact hgen s t
    have hx := hle (hclosure x)
    rw [Subgroup.mem_centralizer_iff] at hx
    exact hx _ rfl
  have hcommC : ∀ a b : FreeGroup S ⧸ C, a * b = b * a := by
    intro a b
    have hle : Subgroup.closure (Set.range fun t : S => QuotientGroup.mk' C (FreeGroup.of t)) ≤
        Subgroup.centralizer {a} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨t, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      rintro _ rfl
      exact (hcentral t a).symm
    have hb := hle (hclosure b)
    rw [Subgroup.mem_centralizer_iff] at hb
    exact hb _ rfl
  letI : CommGroup (FreeGroup S ⧸ C) :=
    { (inferInstance : Group (FreeGroup S ⧸ C)) with mul_comm := hcommC }
  haveI : Group.FG (FreeGroup S) := ProductFinitePresentation.fg_of_isFinitelyPresented _
  haveI : Group.FG (FreeGroup S ⧸ C) := Group.fg_of_surjective (QuotientGroup.mk'_surjective C)
  obtain ⟨T, hT, hTfin⟩ :=
    (Subgroup.fg_iff _).mp (subgroup_fg_of_commGroup (φ.ker.map (QuotientGroup.mk' C)))
  haveI : Finite T := Set.finite_coe_iff.mpr hTfin
  have hTmem : ∀ t ∈ T, t ∈ φ.ker.map (QuotientGroup.mk' C) := fun t ht => by
    rw [← hT]
    exact Subgroup.subset_closure ht
  choose lift hliftK hliftEq using fun t : T => hTmem t t.2
  let R : Set (FreeGroup S) := R₁ ∪ Set.range lift
  have hRK : R ⊆ (φ.ker : Set (FreeGroup S)) := by
    rintro _ (⟨⟨s, t⟩, rfl⟩ | ⟨t, rfl⟩)
    · show φ ⁅FreeGroup.of s, FreeGroup.of t⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact Commute.all _ _
    · exact hliftK t
  have hKle : φ.ker ≤ Subgroup.normalClosure R := by
    intro x hx
    have hmap : φ.ker.map (QuotientGroup.mk' C) ≤
        (Subgroup.normalClosure R).map (QuotientGroup.mk' C) := by
      rw [← hT, Subgroup.closure_le]
      intro t ht
      exact ⟨lift ⟨t, ht⟩, Subgroup.subset_normalClosure (Or.inr ⟨⟨t, ht⟩, rfl⟩), hliftEq ⟨t, ht⟩⟩
    obtain ⟨y, hy, hyx⟩ := hmap ⟨x, hx, rfl⟩
    have hdiff : y⁻¹ * x ∈ C := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have h' : ((y : FreeGroup S) : FreeGroup S ⧸ C) = (x : FreeGroup S ⧸ C) := hyx
      rw [h', inv_mul_cancel]
    have hCle : C ≤ Subgroup.normalClosure R := Subgroup.normalClosure_mono fun r hr => Or.inl hr
    have e : x = y * (y⁻¹ * x) := by group
    rw [e]
    exact (Subgroup.normalClosure R).mul_mem hy (hCle hdiff)
  exact Group.IsFinitelyPresented.of_surjective φ hφ
    ⟨R, (Set.toFinite _).union (Set.toFinite _),
      le_antisymm (Subgroup.normalClosure_le_normal hRK) hKle⟩

/-- **Subgroups of finitely generated commutative groups are finitely presented.** -/
theorem isFinitelyPresented_subgroup_of_commGroup {G : Type*} [CommGroup G] [Group.FG G]
    (H : Subgroup G) : Group.IsFinitelyPresented H := by
  haveI : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr (subgroup_fg_of_commGroup H)
  exact isFinitelyPresented_of_commGroup H

#audit_axioms GroupApproximation.FGAbelianFinitePresentation.isFinitelyPresented_of_commGroup
#audit_axioms GroupApproximation.FGAbelianFinitePresentation.isFinitelyPresented_subgroup_of_commGroup

end FGAbelianFinitePresentation
end GroupApproximation
