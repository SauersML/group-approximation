import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Meta.AxiomGuard

/-!
# Finitary linear groups of a module with a basis

`non_mf_groups_exist.tex`, the remark after `prop:torsion-defect-ring`
(tex lines 1131--1145):

> Let `GL_fs(V^n)` be the group of automorphisms `g` of `V^n` such that `g - I`
> has finite matrix support in this basis … `Rad_MF(EL_n(J)) = EL_n(J,JeJ) ≅
> ⋃_N SL_N(F_2)`, an infinite simple locally finite group.

This module develops the finitary linear group of any vector space `M` with a
basis `B : Module.Basis β F M`, the ambient object of that paragraph.  An automorphism
`g` is *supported on* a finite set `T` of basis indices when it fixes every
basis vector outside `T` and maps the span of the basis vectors in `T` into
itself.  The finitary group is the set of automorphisms supported on some finite
set.

* `supportedOn B T` is a subgroup; inversion uses that an injective endomorphism
  of the finite-dimensional block span is onto.
* `finitary B` is a subgroup, the directed union of the `supportedOn B T`.
* Over a finite field every `supportedOn B T` is finite, so `finitary B` is
  locally finite.
* `mem_finitary_iff_finite_matrixSupport`: the support condition is exactly the
  printed one, that `g - I` has finitely many nonzero matrix entries.
-/

namespace GroupApproximation
namespace FinitaryLinear

universe u v w

variable {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
  {β : Type w} (B : Module.Basis β F M)

/-- The span of the basis vectors indexed by a finite set of indices. -/
def blockSpan (T : Finset β) : Submodule F M :=
  Submodule.span F (B '' (T : Set β))

theorem basis_mem_blockSpan {T : Finset β} {b : β} (hb : b ∈ T) : B b ∈ blockSpan B T :=
  Submodule.subset_span ⟨b, hb, rfl⟩

theorem blockSpan_mono {T T' : Finset β} (h : T ⊆ T') : blockSpan B T ≤ blockSpan B T' :=
  Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr h))

instance blockSpan_finiteDimensional (T : Finset β) : FiniteDimensional F (blockSpan B T) :=
  FiniteDimensional.span_of_finite F (T.finite_toSet.image B)

/-- `g` is supported on the finite index set `T`: it fixes every basis vector
outside `T` and maps the block span of `T` into itself. -/
structure IsSupportedOn (g : M ≃ₗ[F] M) (T : Finset β) : Prop where
  fix : ∀ b, b ∉ T → g (B b) = B b
  maps : ∀ x ∈ blockSpan B T, g x ∈ blockSpan B T

namespace IsSupportedOn

variable {B}

/-- It suffices to check the block span on basis vectors. -/
theorem of_basis {g : M ≃ₗ[F] M} {T : Finset β} (hfix : ∀ b, b ∉ T → g (B b) = B b)
    (hmaps : ∀ b ∈ T, g (B b) ∈ blockSpan B T) : IsSupportedOn B g T where
  fix := hfix
  maps := fun x hx ↦ by
    have hle : blockSpan B T ≤ (blockSpan B T).comap (g : M →ₗ[F] M) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨b, hb, rfl⟩
      exact hmaps b hb
    exact hle hx

/-- Support is monotone in the index set. -/
theorem mono {g : M ≃ₗ[F] M} {T T' : Finset β} (hg : IsSupportedOn B g T) (h : T ⊆ T') :
    IsSupportedOn B g T' := by
  refine of_basis (fun b hb ↦ hg.fix b fun hbT ↦ hb (h hbT)) fun b hb ↦ ?_
  by_cases hbT : b ∈ T
  · exact blockSpan_mono B h (hg.maps _ (basis_mem_blockSpan B hbT))
  · rw [hg.fix b hbT]
    exact basis_mem_blockSpan B hb

theorem one (T : Finset β) : IsSupportedOn B (1 : M ≃ₗ[F] M) T where
  fix := fun _ _ ↦ rfl
  maps := fun _ hx ↦ hx

theorem mul {g h : M ≃ₗ[F] M} {T : Finset β} (hg : IsSupportedOn B g T)
    (hh : IsSupportedOn B h T) : IsSupportedOn B (g * h) T where
  fix := fun b hb ↦ by rw [LinearEquiv.mul_apply, hh.fix b hb, hg.fix b hb]
  maps := fun x hx ↦ by rw [LinearEquiv.mul_apply]; exact hg.maps _ (hh.maps x hx)

/-- The block span is mapped **onto** itself: an injective endomorphism of a
finite-dimensional space is surjective. -/
theorem exists_preimage {g : M ≃ₗ[F] M} {T : Finset β} (hg : IsSupportedOn B g T)
    {x : M} (hx : x ∈ blockSpan B T) : ∃ y ∈ blockSpan B T, g y = x := by
  let r : blockSpan B T →ₗ[F] blockSpan B T := (g : M →ₗ[F] M).restrict hg.maps
  have hinj : Function.Injective r := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact g.injective this
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨x, hx⟩
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem inv {g : M ≃ₗ[F] M} {T : Finset β} (hg : IsSupportedOn B g T) :
    IsSupportedOn B g⁻¹ T where
  fix := fun b hb ↦ by
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_eq]
    exact (hg.fix b hb).symm
  maps := fun x hx ↦ by
    obtain ⟨y, hy, rfl⟩ := hg.exists_preimage hx
    rw [LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
    exact hy

end IsSupportedOn

/-- The automorphisms supported on a fixed finite index set. -/
def supportedOn (T : Finset β) : Subgroup (M ≃ₗ[F] M) where
  carrier := {g | IsSupportedOn B g T}
  one_mem' := IsSupportedOn.one T
  mul_mem' := fun hg hh ↦ hg.mul hh
  inv_mem' := fun hg ↦ hg.inv

theorem mem_supportedOn {T : Finset β} {g : M ≃ₗ[F] M} :
    g ∈ supportedOn B T ↔ IsSupportedOn B g T := Iff.rfl

theorem supportedOn_mono {T T' : Finset β} (h : T ⊆ T') : supportedOn B T ≤ supportedOn B T' :=
  fun _ hg ↦ IsSupportedOn.mono hg h

/-- **The finitary linear group** of `M` in the basis `B`: the automorphisms
supported on some finite set of basis indices. -/
def finitary : Subgroup (M ≃ₗ[F] M) where
  carrier := {g | ∃ T : Finset β, IsSupportedOn B g T}
  one_mem' := ⟨∅, IsSupportedOn.one ∅⟩
  mul_mem' := by
    classical
    rintro g h ⟨T, hg⟩ ⟨T', hh⟩
    exact ⟨T ∪ T', (hg.mono Finset.subset_union_left).mul (hh.mono Finset.subset_union_right)⟩
  inv_mem' := by
    rintro g ⟨T, hg⟩
    exact ⟨T, hg.inv⟩

theorem mem_finitary {g : M ≃ₗ[F] M} : g ∈ finitary B ↔ ∃ T : Finset β, IsSupportedOn B g T :=
  Iff.rfl

theorem supportedOn_le_finitary (T : Finset β) : supportedOn B T ≤ finitary B :=
  fun _ hg ↦ ⟨T, hg⟩

/-! ## The printed condition: finite matrix support of `g - I` -/

/-- The matrix support of an endomorphism in the basis `B`: the index pairs
`(a, b)` with a nonzero entry `B.repr (f (B b)) a`. -/
def matrixSupport (f : M →ₗ[F] M) : Set (β × β) :=
  {p | B.repr (f (B p.2)) p.1 ≠ 0}

/-- **The printed condition.**  `g` lies in the finitary group exactly when
`g - I` has finitely many nonzero matrix entries in the basis `B`. -/
theorem mem_finitary_iff_finite_matrixSupport (g : M ≃ₗ[F] M) :
    g ∈ finitary B ↔ (matrixSupport B ((g : M →ₗ[F] M) - LinearMap.id)).Finite := by
  classical
  constructor
  · rintro ⟨T, hg⟩
    refine Set.Finite.subset ((T ×ˢ T : Finset (β × β)).finite_toSet) ?_
    rintro ⟨a, b⟩ hab
    simp only [matrixSupport, Set.mem_setOf_eq, LinearMap.sub_apply, LinearEquiv.coe_coe,
      LinearMap.id_apply] at hab
    have hb : b ∈ T := by
      by_contra hbT
      exact hab (by rw [hg.fix b hbT, sub_self, map_zero, Finsupp.zero_apply])
    have hmem : g (B b) - B b ∈ blockSpan B T :=
      Submodule.sub_mem _ (hg.maps _ (basis_mem_blockSpan B hb)) (basis_mem_blockSpan B hb)
    have hsupp := (Module.Basis.mem_span_image B).mp hmem
    have ha : a ∈ T := by
      have : a ∈ (B.repr (g (B b) - B b)).support := Finsupp.mem_support_iff.mpr hab
      exact_mod_cast hsupp this
    simp [Finset.coe_product, ha, hb]
  · intro hfin
    let T : Finset β := (hfin.image Prod.fst).toFinset ∪ (hfin.image Prod.snd).toFinset
    refine ⟨T, IsSupportedOn.of_basis (fun b hb ↦ ?_) fun b hb ↦ ?_⟩
    · -- no nonzero entry in column `b`
      have hzero : B.repr (g (B b) - B b) = 0 := by
        ext a
        by_contra hne
        apply hb
        refine Finset.mem_union_right _ ?_
        rw [Set.Finite.mem_toFinset]
        exact ⟨(a, b), by simpa [matrixSupport] using hne, rfl⟩
      have := B.repr.injective (hzero.trans (map_zero B.repr).symm)
      exact sub_eq_zero.mp this
    · have hmem : g (B b) - B b ∈ blockSpan B T := by
        refine (Module.Basis.mem_span_image B).mpr ?_
        intro a ha
        refine Finset.mem_union_left _ ?_
        rw [Set.Finite.mem_toFinset]
        exact ⟨(a, b), by simpa [matrixSupport] using Finsupp.mem_support_iff.mp ha, rfl⟩
      have := Submodule.add_mem _ hmem (basis_mem_blockSpan B hb)
      simpa using this

/-! ## Local finiteness over a finite field -/

/-- Over a finite field every block stabilizer is finite: an automorphism
supported on `T` is determined by the images of the finitely many basis vectors
in `T`, which lie in the finite block span. -/
theorem finite_supportedOn [Finite F] (T : Finset β) : Finite (supportedOn B T) := by
  classical
  haveI : Finite (blockSpan B T) := Module.finite_of_finite F
  let f : supportedOn B T → (T → blockSpan B T) := fun g b ↦
    ⟨(g : M ≃ₗ[F] M) (B b), ((mem_supportedOn B).mp g.2).maps _ (basis_mem_blockSpan B b.2)⟩
  refine Finite.of_injective f ?_
  intro g h hgh
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  refine B.ext fun b ↦ ?_
  by_cases hb : b ∈ T
  · have := congrArg Subtype.val (congrFun hgh ⟨b, hb⟩)
    simpa [f] using this
  · simp only [LinearEquiv.coe_coe]
    rw [((mem_supportedOn B).mp g.2).fix b hb, ((mem_supportedOn B).mp h.2).fix b hb]

/-- **Over a finite field the finitary group is locally finite.** -/
theorem isLocallyFiniteGroup_finitary [Finite F] : IsLocallyFiniteGroup (finitary B) := by
  classical
  intro s
  choose T hT using fun g : finitary B ↦ (g.2 : ∃ T : Finset β, IsSupportedOn B g T)
  let U : Finset β := s.biUnion T
  refine ⟨(supportedOn B U).subgroupOf (finitary B), ?_, fun g hg ↦ ?_⟩
  · haveI := finite_supportedOn B U
    exact Finite.of_injective
      (fun x : (supportedOn B U).subgroupOf (finitary B) ↦
        (⟨((x : finitary B) : M ≃ₗ[F] M), x.2⟩ : supportedOn B U))
      (fun x y hxy ↦ Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy)))
  · rw [Subgroup.mem_subgroupOf]
    exact (hT g).mono (Finset.subset_biUnion_of_mem T hg)

end FinitaryLinear
end GroupApproximation

#audit_axioms GroupApproximation.FinitaryLinear.mem_finitary_iff_finite_matrixSupport
#audit_axioms GroupApproximation.FinitaryLinear.isLocallyFiniteGroup_finitary
