import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Tietze transformations: finite presentability does not depend on the generators

Lemma 54.3 needs one fact about finite presentations, and it is the fact Tietze
transformations exist to supply:

> if a group is finitely presented at all, then for **every** finite generating
> set the corresponding kernel is the normal closure of a finite set;

and its consequence for a surjection,

> if `E ↠ W` with `E` finitely generated and `W` finitely presented on the
> induced generators, then the kernel is finitely normally generated.

Mathlib has `PresentedGroup` but no Tietze transformations, so both are proved
here, and neither needs any bureaucracy about presentations as objects: the
whole content is visible at the level of free groups.

`ker_eq_normalClosure` is the first statement.  Its proof is the usual pair of
translation maps.  Write the old generators as words in the new ones and the new
in the old, giving `φ : F(S) → F(S₀)` and `ψ : F(S₀) → F(S)` compatible with the
two presentations.  The new relators are the translated old relators together
with the finitely many *translation relators* `s⁻¹ · ψ(φ(s))`, one per new
generator, which say exactly that going to the old alphabet and back is the
identity.  Modulo those, `ψ ∘ φ` is the identity, so a word killed by the new
presentation map has `φ` of it killed by the old one, hence lying in the old
relator closure, and pulling back with `ψ` lands in the new closure.

Notably no surjectivity hypothesis appears: the translation maps carry all the
information that is needed.

`ker_eq_normalClosure_image` is the second statement, and
`normalClosure_image_finite` records that the relator sets stay finite, which is
what makes the conclusion a *finite* normal generation.
-/

namespace GroupApproximation

namespace Tietze

universe u v w

/-! ## Two homomorphisms out of a free group agreeing on generators -/

/-- Homomorphisms out of a free group are determined by their values on the
generators. -/
theorem freeGroup_hom_ext {S : Type u} {Q : Type v} [Group Q]
    {g₁ g₂ : FreeGroup S →* Q}
    (h : ∀ s, g₁ (FreeGroup.of s) = g₂ (FreeGroup.of s)) : g₁ = g₂ := by
  refine MonoidHom.ext fun w => ?_
  rw [FreeGroup.lift_unique g₁ (f := fun s => g₂ (FreeGroup.of s)) h,
    ← FreeGroup.lift_unique g₂ (f := fun s => g₂ (FreeGroup.of s)) (fun _ => rfl)]

/-! ## Normal closures under homomorphisms -/

/-- The image of a normal closure lies in the normal closure of the image. -/
theorem map_normalClosure_le {F : Type u} [Group F] {E : Type v} [Group E]
    (ψ : F →* E) (S : Set F) :
    (Subgroup.normalClosure S).map ψ ≤ Subgroup.normalClosure (ψ '' S) := by
  rw [Subgroup.map_le_iff_le_comap]
  exact Subgroup.normalClosure_le_normal
    (fun s hs => Subgroup.subset_normalClosure ⟨s, hs, rfl⟩)

/-! ## Changing the generating set -/

section ChangeOfGenerators

variable {S : Type u} {S₀ : Type v} {W : Type w} [Group W]

/-- **Tietze's theorem, in the form Lemma 54.3 uses.**  Suppose `W` is presented
on the alphabet `S₀` with relator set `R₀`, and `π` is any presentation map on a
second alphabet `S`.  Given translations `f` of the new generators into the old
and `g` of the old into the new, compatible with both presentation maps, the
kernel of `π` is the normal closure of the translated relators together with one
translation relator per new generator.

In particular, if `R₀` and `S` are finite then so is that set, which is the
statement that finite presentability is independent of the finite generating
set. -/
theorem ker_eq_normalClosure
    (π₀ : FreeGroup S₀ →* W) (R₀ : Set (FreeGroup S₀))
    (hR₀ : π₀.ker = Subgroup.normalClosure R₀)
    (π : FreeGroup S →* W)
    (f : S → FreeGroup S₀) (hf : ∀ s, π₀ (f s) = π (FreeGroup.of s))
    (g : S₀ → FreeGroup S) (hg : ∀ t, π (g t) = π₀ (FreeGroup.of t)) :
    π.ker = Subgroup.normalClosure
      ((FreeGroup.lift g) '' R₀ ∪
        Set.range fun s : S =>
          (FreeGroup.of s)⁻¹ * FreeGroup.lift g (FreeGroup.lift f (FreeGroup.of s))) := by
  classical
  set φ : FreeGroup S →* FreeGroup S₀ := FreeGroup.lift f with hφdef
  set ψ : FreeGroup S₀ →* FreeGroup S := FreeGroup.lift g with hψdef
  set T : Set (FreeGroup S) :=
    (ψ : FreeGroup S₀ → FreeGroup S) '' R₀ ∪
      Set.range fun s : S => (FreeGroup.of s)⁻¹ * ψ (φ (FreeGroup.of s)) with hTdef
  -- the two translation identities, as homomorphisms
  have hπ₀φ : π₀.comp φ = π := by
    refine freeGroup_hom_ext fun s => ?_
    simpa [hφdef] using hf s
  have hπψ : π.comp ψ = π₀ := by
    refine freeGroup_hom_ext fun t => ?_
    simpa [hψdef] using hg t
  have hR₀ker : R₀ ⊆ (π₀.ker : Set (FreeGroup S₀)) := by
    rw [hR₀]
    exact Subgroup.subset_normalClosure
  refine le_antisymm ?_ ?_
  · -- the hard inclusion
    intro w hw
    have hφw : φ w ∈ Subgroup.normalClosure R₀ := by
      rw [← hR₀, MonoidHom.mem_ker, ← MonoidHom.comp_apply, hπ₀φ]
      exact MonoidHom.mem_ker.mp hw
    have hψφw : ψ (φ w) ∈ Subgroup.normalClosure T := by
      refine Subgroup.normalClosure_mono Set.subset_union_left ?_
      exact map_normalClosure_le ψ R₀ ⟨φ w, hφw, rfl⟩
    -- modulo `T` the composite `ψ ∘ φ` is the identity
    have hquot : (QuotientGroup.mk' (Subgroup.normalClosure T)).comp (ψ.comp φ)
        = QuotientGroup.mk' (Subgroup.normalClosure T) := by
      refine freeGroup_hom_ext fun s => ?_
      have hrel : (FreeGroup.of s)⁻¹ * ψ (φ (FreeGroup.of s))
          ∈ Subgroup.normalClosure T :=
        Subgroup.subset_normalClosure (Or.inr ⟨s, rfl⟩)
      have hinv := (Subgroup.normalClosure T).inv_mem hrel
      rw [mul_inv_rev, inv_inv] at hinv
      exact QuotientGroup.eq.mpr hinv
    have := congrArg (fun k : FreeGroup S →* _ => k w) hquot
    simp only [MonoidHom.comp_apply] at this
    have hzero : (QuotientGroup.mk' (Subgroup.normalClosure T)) (ψ (φ w)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hψφw
    rw [hzero] at this
    exact (QuotientGroup.eq_one_iff _).mp this.symm
  · -- the easy inclusion
    refine Subgroup.normalClosure_le_normal ?_
    rintro w (⟨r, hr, rfl⟩ | ⟨s, rfl⟩)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, ← MonoidHom.comp_apply, hπψ]
      exact MonoidHom.mem_ker.mp (hR₀ker hr)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv,
        ← MonoidHom.comp_apply, hπψ, ← MonoidHom.comp_apply (f := φ), hπ₀φ,
        inv_mul_cancel]

end ChangeOfGenerators

/-! ## Kernels of surjections -/

/-- **Transfer along a surjection.**  If the kernel of `q ∘ π` is normally
generated by `T`, then the kernel of `q` is normally generated by the image of
`T`.  With `T` finite this is the statement that the kernel of a surjection
between finitely presented groups is *finitely* normally generated -- the step
Lemma 54.3 calls "finite Tietze transformations". -/
theorem ker_eq_normalClosure_image {F : Type u} [Group F] {E : Type v} [Group E]
    {W : Type w} [Group W] (π : F →* E) (hπ : Function.Surjective π)
    (q : E →* W) (T : Set F) (hT : (q.comp π).ker = Subgroup.normalClosure T) :
    q.ker = Subgroup.normalClosure (π '' T) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨z, rfl⟩ := hπ y
    have hz : z ∈ Subgroup.normalClosure T := by
      rw [← hT, MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact MonoidHom.mem_ker.mp hy
    exact map_normalClosure_le π T ⟨z, hz, rfl⟩
  · refine Subgroup.normalClosure_le_normal ?_
    rintro _ ⟨t, ht, rfl⟩
    have : t ∈ (q.comp π).ker := by
      rw [hT]
      exact Subgroup.subset_normalClosure ht
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.mp this

/-- The relator set produced by `ker_eq_normalClosure_image` is finite whenever
the one it comes from is. -/
theorem normalClosure_image_finite {F : Type u} [Group F] {E : Type v} [Group E]
    (π : F →* E) {T : Set F} (hT : Set.Finite T) : Set.Finite (π '' T) :=
  Set.Finite.image _ hT

end Tietze

end GroupApproximation
