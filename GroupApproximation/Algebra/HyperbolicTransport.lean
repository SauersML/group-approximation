import GroupApproximation.Algebra.HyperbolicGroup

/-!
# Hyperbolicity is an isomorphism invariant

`Algebra/HyperbolicGroup.lean` defines `IsHyperbolicGroup G` by asking for *some*
finite symmetric alphabet whose word metric satisfies the four-point condition.
A definition of that shape owes the reader at least this much: that it is a
property of the group and not of the alphabet.  This module supplies it.

## What is proved

`IsHyperbolicGroup.of_mulEquiv` --- an isomorphism carries a hyperbolic group to
a hyperbolic group, with the same constant, by transporting the alphabet.  The
route is the exact transport of the word metric,
`wordDist_image_mulEquiv`: an isomorphism is a bijection on words, so it changes
no word length at all, and the four-point condition is then transported
literally rather than up to a constant.

The word-metric lemmas (`isWord_map`, `wordNorm_map_le`,
`isSymmetricGeneratingSet_image`) are general facts about homomorphisms and are
stated here rather than in `Algebra/WordMetric.lean` only to keep that shared
module untouched.

## What is *not* proved

That hyperbolicity does not depend on the choice of finite generating set.  That
is quasi-isometry invariance, whose proof needs stability of quasi-geodesics ---
the Morse lemma.  `Algebra/WordMetricComparison.lean` carries the two
prerequisites that are elementary (bi-Lipschitz comparison of alphabets, and the
subword property of geodesic words); the Morse lemma itself is the input neither
Mathlib nor this repository has.  The existential form of `IsHyperbolicGroup` is
chosen precisely so that nothing downstream needs the missing theorem.
-/

namespace GroupApproximation
namespace Hyperbolic

open WordMetric

universe u v

section Map

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- A word pushes forward along a homomorphism, over the image alphabet. -/
theorem isWord_map (f : G →* H) {S : Set G} {l : List G} {g : G} (h : IsWord S l g) :
    IsWord (f '' S) (l.map f) (f g) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Set.mem_image_of_mem f (h.letters y hy)
  · rw [List.prod_hom, h.prod_eq]

/-- The image of a symmetric generating set under a surjective homomorphism is a
symmetric generating set. -/
theorem isSymmetricGeneratingSet_image (f : G →* H) (hf : Function.Surjective f)
    {S : Set G} (hS : IsSymmetricGeneratingSet S) :
    IsSymmetricGeneratingSet (f '' S) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨y⁻¹, hS.inv_mem y hy, map_inv f y⟩
  · rw [← Subgroup.map_closure, hS.closure_eq]
    exact Subgroup.map_top_of_surjective f hf

/-- Pushing a spelling forward can only shorten it. -/
theorem wordNorm_map_le (f : G →* H) {S : Set G} (hS : IsSymmetricGeneratingSet S) (g : G) :
    wordNorm (f '' S) (f g) ≤ wordNorm S g := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS g
  have h := wordNorm_le_length (isWord_map f hl)
  rw [List.length_map, hlen] at h
  exact h

end Map

section Equiv

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The monoid homomorphism underlying an isomorphism is surjective. -/
theorem surjective_mulEquiv_toMonoidHom (e : G ≃* H) :
    Function.Surjective (e : G →* H) := fun y => ⟨e.symm y, by simp⟩

/-- Transporting an alphabet forward and back returns it. -/
theorem image_symm_image (e : G ≃* H) (S : Set G) :
    (e.symm : H →* G) '' ((e : G →* H) '' S) = S := by
  rw [Set.image_image]
  simp

/-- **Word length is an isomorphism invariant**, at the transported alphabet:
shortening in both directions forces equality. -/
theorem wordNorm_image_mulEquiv (e : G ≃* H) {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (g : G) :
    wordNorm ((e : G →* H) '' S) ((e : G →* H) g) = wordNorm S g := by
  refine le_antisymm (wordNorm_map_le (e : G →* H) hS g) ?_
  have hSimg : IsSymmetricGeneratingSet ((e : G →* H) '' S) :=
    isSymmetricGeneratingSet_image _ (surjective_mulEquiv_toMonoidHom e) hS
  have h := wordNorm_map_le (e.symm : H →* G) hSimg ((e : G →* H) g)
  have hsymm : (e.symm : H →* G) ((e : G →* H) g) = g := by simp
  rw [image_symm_image, hsymm] at h
  exact h

/-- **The word metric is an isomorphism invariant.** -/
theorem wordDist_image_mulEquiv (e : G ≃* H) {S : Set G} (hS : IsSymmetricGeneratingSet S)
    (a b : G) :
    wordDist ((e : G →* H) '' S) ((e : G →* H) a) ((e : G →* H) b) = wordDist S a b := by
  have hmul : ((e : G →* H) a)⁻¹ * ((e : G →* H) b) = (e : G →* H) (a⁻¹ * b) := by
    simp
  show wordNorm ((e : G →* H) '' S) (((e : G →* H) a)⁻¹ * ((e : G →* H) b))
      = wordNorm S (a⁻¹ * b)
  rw [hmul, wordNorm_image_mulEquiv e hS]

/-- **Hyperbolicity is an isomorphism invariant**, with the same constant: the
transported alphabet has the same word metric, so it satisfies the same
four-point condition. -/
theorem IsHyperbolicGroup.of_mulEquiv (e : G ≃* H) (h : IsHyperbolicGroup G) :
    IsHyperbolicGroup H := by
  classical
  obtain ⟨S, hS, δ, hδ⟩ := h
  have hcoe : ((S.image (e : G →* H) : Finset H) : Set H)
      = (e : G →* H) '' (S : Set G) := by
    simp
  refine ⟨S.image (e : G →* H), ?_, δ, ?_⟩
  · rw [hcoe]
    exact isSymmetricGeneratingSet_image _ (surjective_mulEquiv_toMonoidHom e) hS
  · rw [hcoe]
    intro w x y z
    obtain ⟨w', rfl⟩ := surjective_mulEquiv_toMonoidHom e w
    obtain ⟨x', rfl⟩ := surjective_mulEquiv_toMonoidHom e x
    obtain ⟨y', rfl⟩ := surjective_mulEquiv_toMonoidHom e y
    obtain ⟨z', rfl⟩ := surjective_mulEquiv_toMonoidHom e z
    simp only [wordDist_image_mulEquiv e hS]
    exact hδ w' x' y' z'

end Equiv

end Hyperbolic
end GroupApproximation
