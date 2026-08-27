import GroupApproximation.Computability.PresentationCodeList
import GroupApproximation.Computability.RabinConstructionSource
import GroupApproximation.Algebra.PresentedGroupRelabel
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The free product of two codes

The variant Adian--Rabin construction embeds its *source* group in the group it
outputs whenever the word survives.  For that to force a failure of operator-MF
the source has to contain a group known not to be MF, so the source of the
reduction is not the input group but its free product with the manuscript's
finitely presented non-MF group.

This file performs that free product at the level of codes.  Everything is
built from lists and from `finSumFinEquiv`, so the code is a computable
function of the two inputs, and `coprodCodeEquiv` identifies the group it
presents with `RabinConstructionSource.CoprodPresented`, where the two factor
embeddings and the two word-problem restrictions already live.

`wordOf_coprodCode` is the one piece of arithmetic: a code reads a letter by
reducing its index modulo the alphabet size, so a word written for the smaller
alphabet is read differently by the larger code unless its letters are already
in range.  `normWord` puts them in range without changing what the smaller code
reads, and then the two readings agree on the nose.
-/

namespace GroupApproximation
namespace CoprodCode

open PresentationCodes PresentationCodeList PresentedGroupRelabel RabinConstructionSource

/-! ## The code -/

/-- The relators of the free product, over the disjoint alphabet. -/
def coprodList (c d : PresentationCode) :
    List (FreeGroup (Fin (genCount c) ⊕ Fin (genCount d))) :=
  (relatorListOf c).map (FreeGroup.map Sum.inl) ++
    (relatorListOf d).map (FreeGroup.map Sum.inr)

/-- The relators of the free product, renumbered. -/
def coprodRelators (c d : PresentationCode) :
    List (FreeGroup (Fin (genCount c + genCount d))) :=
  (coprodList c d).map (relabel finSumFinEquiv)

/-- **The code of the free product.** -/
abbrev coprodCode (c d : PresentationCode) : PresentationCode :=
  codeOfList (m := genCount c + d.1) (coprodRelators c d)

/-- The list spells the free product's relator set. -/
theorem setOf_mem_coprodList (c d : PresentationCode) :
    {x | x ∈ coprodList c d}
      = coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d} := by
  ext x
  simp only [coprodList, coprodRels, List.mem_append, List.mem_map, Set.mem_union,
    Set.mem_image, Set.mem_setOf_eq]

/-- **The code presents the free product.** -/
noncomputable def coprodCodeEquiv (c d : PresentationCode) :
    Carrier (coprodCode c d) ≃*
      CoprodPresented {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d} :=
  ((carrierOfList (coprodRelators c d)).trans
      (presCongrSet (setOf_mem_map _ _))).trans
    (((congrEquiv (finSumFinEquiv (m := genCount c) (n := genCount d))
        {x | x ∈ coprodList c d}).symm).trans
      (presCongrSet (setOf_mem_coprodList c d)))

/-- **The relator set of the free-product code**, as a renumbering of the
free-product relators. -/
theorem relSet_coprodCode (c d : PresentationCode) :
    {x | x ∈ relatorListOf (coprodCode c d)}
      = relabelRels (finSumFinEquiv (m := genCount c) (n := genCount d))
          (coprodRels {x | x ∈ relatorListOf c} {x | x ∈ relatorListOf d}) := by
  have h1 : {x | x ∈ relatorListOf (coprodCode c d)} = {x | x ∈ coprodRelators c d} := by
    rw [← coe_relatorFinset, coe_relatorFinset_codeOfList]
    rfl
  rw [h1, coprodRelators, setOf_mem_map, setOf_mem_coprodList]
  rfl

/-! ## Reading a word of the left factor -/

/-- A word with its letters reduced into the left factor's alphabet. -/
def normWord (c : PresentationCode) (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  w.map fun p => (p.1 % genCount c, p.2)

theorem letterOf_normWord (c : PresentationCode) (i : ℕ) :
    letterOf c (i % genCount c) = letterOf c i := by
  apply Fin.ext
  show (i % genCount c) % genCount c = i % genCount c
  exact Nat.mod_mod_of_dvd i dvd_rfl

/-- Normalizing the letters does not change what the code reads. -/
theorem wordOf_normWord (c : PresentationCode) (w : List (ℕ × Bool)) :
    wordOf c (normWord c w) = wordOf c w := by
  show FreeGroup.mk _ = FreeGroup.mk _
  congr 1
  simp only [normWord, List.map_map, Function.comp_def, letterOf_normWord]

/-- **The larger code reads a normalized word as the image of the smaller
reading.**  Letters below the left alphabet's size survive both reductions, and
`finSumFinEquiv` on a left injection preserves the underlying number. -/
theorem wordOf_coprodCode (c d : PresentationCode) (w : List (ℕ × Bool)) :
    wordOf (coprodCode c d) (normWord c w)
      = relabel (finSumFinEquiv (m := genCount c) (n := genCount d))
          (FreeGroup.map Sum.inl (wordOf c w)) := by
  show FreeGroup.mk _ = _
  rw [wordOf, FreeGroup.map.mk, relabel, FreeGroup.map.mk]
  congr 1
  simp only [normWord, List.map_map, Function.comp_def]
  refine List.map_congr_left fun p _ => ?_
  refine Prod.ext ?_ rfl
  apply Fin.ext
  have hlt : p.1 % genCount c < genCount c := Nat.mod_lt _ (genCount_pos c)
  have hgc : genCount (coprodCode c d) = genCount c + genCount d := rfl
  have hval : ((finSumFinEquiv (Sum.inl (letterOf c p.1)) :
      Fin (genCount c + genCount d)) : ℕ)
      = ((letterOf c p.1 : Fin (genCount c)) : ℕ) := by simp
  show (p.1 % genCount c) % genCount (coprodCode c d)
    = ((finSumFinEquiv (Sum.inl (letterOf c p.1))) : ℕ)
  rw [hgc, Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.le_add_right _ _)), hval]
  rfl

end CoprodCode
end GroupApproximation
