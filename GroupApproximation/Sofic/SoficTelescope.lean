import GroupApproximation.Algebra.MappingTelescope

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

end GroupApproximation
