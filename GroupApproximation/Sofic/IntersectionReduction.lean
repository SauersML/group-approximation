import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Countable.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Reducing subgroup intersections in a countable group

An arbitrary family of subgroups of a countable group has a countable
subfamily with the same intersection.  The proof chooses, for every element
outside the total intersection, one subgroup which excludes that element.

This is the purely algebraic countability step in intersection-permanence
arguments for relative approximation properties.  It has no approximation,
amenability, or operator-algebraic hypotheses.
-/

namespace GroupApproximation

open scoped Pointwise

variable {G : Type*} [Group G]

noncomputable local instance subgroupIInfNormal
    {I : Type*} (N : I → Subgroup G) [∀ i, (N i).Normal] :
    (⨅ i, N i).Normal :=
  Subgroup.normal_iInf_normal fun _ ↦ inferInstance

noncomputable local instance subgroupOfNormal
    (N K : Subgroup G) [N.Normal] : (N.subgroupOf K).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (by
    rw [N.normalizer_eq_top]
    exact le_top)

/-- In a countable group, an arbitrary intersection of subgroups is already
the intersection of a countable subfamily. -/
theorem Subgroup.exists_countable_subfamily_iInf_eq [Countable G]
    {I : Type*} (K : I → Subgroup G) :
    ∃ J : Set I, Set.Countable J ∧ (⨅ j : J, K j.1) = ⨅ i, K i := by
  classical
  let total : Subgroup G := ⨅ i, K i
  let bad : Set G := {g | g ∉ total}
  have hexclude : ∀ g : bad, ∃ i, (g : G) ∉ K i := by
    intro g
    have hg : (g : G) ∉ ⨅ i, K i := by
      have hbad := g.property
      change (g : G) ∉ total at hbad
      simpa only [total] using hbad
    simpa only [Subgroup.mem_iInf, not_forall] using hg
  let exclude : bad → I := fun g ↦ Classical.choose (hexclude g)
  have hexclude_spec (g : bad) : (g : G) ∉ K (exclude g) :=
    Classical.choose_spec (hexclude g)
  let J : Set I := Set.range exclude
  refine ⟨J, Set.countable_range exclude, le_antisymm ?_ ?_⟩
  · intro g hg
    rw [Subgroup.mem_iInf] at hg
    rw [Subgroup.mem_iInf]
    intro i
    by_contra hgi
    have hbad : g ∈ bad := by
      simpa only [bad, total, Subgroup.mem_iInf, not_forall] using ⟨i, hgi⟩
    let gbad : bad := ⟨g, hbad⟩
    have hJ : exclude gbad ∈ J := ⟨gbad, rfl⟩
    have hmem : g ∈ K (exclude gbad) := by
      have := hg ⟨exclude gbad, hJ⟩
      simpa only using this
    exact hexclude_spec gbad hmem
  · exact le_iInf fun j ↦ iInf_le K j.1

/-! ## Finite and arbitrary diagonal quotient maps -/

/-- The diagonal map from a group to the product of a family of quotient
groups. -/
noncomputable def Subgroup.quotientDiagonal
    {I : Type*} (N : I → Subgroup G) [∀ i, (N i).Normal] :
    G →* ∀ i, G ⧸ N i :=
  MonoidHom.pi fun i ↦ QuotientGroup.mk' (N i)

@[simp]
theorem Subgroup.quotientDiagonal_apply
    {I : Type*} (N : I → Subgroup G) [∀ i, (N i).Normal]
    (g : G) (i : I) :
    quotientDiagonal N g i = QuotientGroup.mk g :=
  rfl

/-- The kernel of the diagonal quotient map is exactly the intersection of
the quotient kernels. -/
theorem Subgroup.ker_quotientDiagonal
    {I : Type*} (N : I → Subgroup G) [∀ i, (N i).Normal] :
    (quotientDiagonal N).ker = ⨅ i, N i := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_iInf]
  constructor
  · intro hg i
    have hi := congrFun hg i
    simpa only [quotientDiagonal_apply, Pi.one_apply,
      QuotientGroup.eq_one_iff] using hi
  · intro hg
    ext i
    simpa only [quotientDiagonal_apply, Pi.one_apply,
      QuotientGroup.eq_one_iff] using hg i

/-- The quotient by an intersection embeds diagonally into the product of
the individual quotients. -/
noncomputable def Subgroup.quotientIInfHom
    {I : Type*} (N : I → Subgroup G) [∀ i, (N i).Normal] :
    (G ⧸ ⨅ i, N i) →* ∀ i, G ⧸ N i :=
  QuotientGroup.lift (⨅ i, N i) (quotientDiagonal N) (by
    rw [ker_quotientDiagonal])

/-- The diagonal quotient homomorphism is injective. -/
theorem Subgroup.quotientIInfHom_injective
    {I : Type*} (N : I → Subgroup G) [∀ i, (N i).Normal] :
    Function.Injective (quotientIInfHom N) := by
  apply (QuotientGroup.injective_lift_iff
    (N := ⨅ i, N i) (quotientDiagonal N) (by
      rw [ker_quotientDiagonal])).2
  exact (ker_quotientDiagonal N).symm

/-- Inclusion of subgroups induces an injective homomorphism on quotients by
the restriction of one ambient normal subgroup. -/
theorem Subgroup.quotientMapSubgroupOfOfLe_injective
    (N K L : Subgroup G) [N.Normal] (hKL : K ≤ L) :
    Function.Injective
      (QuotientGroup.quotientMapSubgroupOfOfLe (le_refl N) hKL) := by
  exact (Subgroup.quotientSubgroupOfEmbeddingOfLE N hKL).injective

/-- Simultaneously include an intersection subgroup into each member of a
family and quotient by the corresponding ambient-normal subgroup. -/
noncomputable def Subgroup.quotientSubgroupIInfHom
    {I : Type*} (N K : I → Subgroup G) [∀ i, (N i).Normal] :
    (↑(⨅ i, K i) ⧸ Subgroup.subgroupOf (⨅ i, N i) (⨅ i, K i)) →*
      ∀ i, K i ⧸ (N i).subgroupOf (K i) :=
  MonoidHom.pi fun i ↦
    QuotientGroup.quotientMapSubgroupOfOfLe (iInf_le N i) (iInf_le K i)

/-- The simultaneous quotient-inclusion map is injective. -/
theorem Subgroup.quotientSubgroupIInfHom_injective
    {I : Type*} (N K : I → Subgroup G) [∀ i, (N i).Normal] :
    Function.Injective (quotientSubgroupIInfHom N K) := by
  intro q
  refine QuotientGroup.induction_on q fun x ↦ ?_
  intro r
  refine QuotientGroup.induction_on r fun y ↦ ?_
  intro hxy
  rw [QuotientGroup.eq]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_iInf]
  intro i
  have hi := congrFun hxy i
  change
    QuotientGroup.quotientMapSubgroupOfOfLe (iInf_le N i) (iInf_le K i)
        (QuotientGroup.mk x) =
      QuotientGroup.quotientMapSubgroupOfOfLe (iInf_le N i) (iInf_le K i)
        (QuotientGroup.mk y) at hi
  rw [
    QuotientGroup.quotientMapSubgroupOfOfLe_mk,
    QuotientGroup.quotientMapSubgroupOfOfLe_mk, QuotientGroup.eq] at hi
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_inclusion] using hi

end GroupApproximation
