import GroupApproximation.Algebra.MappingTelescope
import GroupApproximation.Sofic.SoficDirectedUnion
import GroupApproximation.Sofic.SoficTransfer

/-!
# Soficity of a mapping telescope

The mapping telescope of an injective endomorphism is the increasing union of
its level copies of the base group, and each level copy is a faithful copy of
that group.  Soficity is local, so the telescope inherits it: a finite window
is carried by finitely many levels, and raising every element to the largest
of them puts the whole window inside one level.

This is the middle layer of the sofic-witness tower: the base is sofic, the
telescope of the compressing endomorphism is therefore sofic, and the Clifford
lamps and the shift are added on top of it.
-/

namespace GroupApproximation

open MappingTelescope

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

include hα in
/-- Every element of the telescope lies at some level. -/
theorem exists_level_repr (g : Telescope α hα) :
    ∃ (n : ℕ) (x : Γ), level α hα n x = g := by
  obtain ⟨p, hp⟩ := mk_surjective α hα g
  exact ⟨p.1, p.2, hp⟩

include hα in
/-- A level copy absorbs everything below it. -/
theorem level_mem_range_of_le {n N : ℕ} (hn : n ≤ N) (x : Γ) :
    level α hα n x ∈ (level α hα N).range := by
  refine ⟨iterateHom α (N - n) x, ?_⟩
  have hN : n + (N - n) = N := by omega
  show mk α hα N (iterateHom α (N - n) x) = mk α hα n x
  simpa only [hN] using (mk_add_iterate α hα n (N - n) x).symm

include hα in
/-- Each level copy of the base group is sofic when the base group is. -/
theorem isSofic_level_range (hΓ : IsSofic Γ) (n : ℕ) :
    IsSofic ((level α hα n).range) := by
  have hequiv : Γ ≃* (level α hα n).range :=
    MonoidHom.ofInjective (level_injective α hα n)
  exact isSofic_of_injective (hequiv.symm.toMonoidHom)
    hequiv.symm.injective hΓ

include hα in
/-- **The mapping telescope of a sofic group is sofic.** -/
theorem isSofic_telescope (hΓ : IsSofic Γ) : IsSofic (Telescope α hα) := by
  classical
  apply isSofic_of_every_finset_mem_sofic_subgroup
  intro F
  -- choose a level representative for every element of the telescope
  choose lvl elt hrepr using exists_level_repr α hα
  refine ⟨(level α hα (F.sup lvl)).range, isSofic_level_range α hα hΓ _, ?_⟩
  intro g hg
  have hle : lvl g ≤ F.sup lvl := Finset.le_sup (f := lvl) hg
  have := level_mem_range_of_le α hα (N := F.sup lvl) hle (elt g)
  rwa [hrepr g] at this

end GroupApproximation
