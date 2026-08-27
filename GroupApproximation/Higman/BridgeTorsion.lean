import GroupApproximation.Higman.HNNEmbedding
import GroupApproximation.Higman.ChiodoReduction
import GroupApproximation.Higman.CoprodTorsion
import GroupApproximation.Higman.EvalRaw
import GroupApproximation.GroupTheory.HNNBrittonCyclic

/-!
# The bridge, and its torsion clause discharged

`Higman.HNNEmb.nonempty_fgOvergroup` proves the group theory of the
Higman--Neumann--Neumann bridge: every countable group embeds in a
three-generator group.  Chiodo's Theorem 2.2 needs two further clauses of the
same construction --- that the overgroup is still torsion-free, and that it is
still recursively presented.

**The torsion clause is a theorem here, not an input.**  The construction is
`Ext g = (A ∗ F₂) ∗_ψ t`, so it needs exactly:

* a free product of torsion-free groups is torsion-free --- proved, at the
  indexed free product in `Algebra.CoprodICyclicReduction` and carried to the
  binary one by `Higman.isPowerTorsionFree_coprod`;
* an HNN extension of a torsion-free group is torsion-free --- proved, as
  `HNNBritton.isPowerTorsionFree_hnn`, off this repository's own cyclic
  reduction lemma;
* a free group is torsion-free --- Mathlib's `FreeGroup` instance.

What is left of the bridge is therefore the effectivity clause alone,
`BridgeRecursive`, and `countableToFG_of_input` builds `Higman.CountableToFG`
from it.
-/

namespace GroupApproximation
namespace Higman

open scoped Monoid.Coprod

/-- **Input: the effectivity clause of the bridge.**  The three-generator
overgroup of a recursively presented countable group is recursively presented;
the intended enumeration `g` is the one running over words in the given
generators, so that the datum is effective.

**Nothing inhabits this structure.** -/
structure BridgeRecursive where
  /-- The overgroup is recursively presented. -/
  recursive : ∀ (A : Type) [Group A] (g : ℕ → A), RecursivePresentation A →
    Function.Surjective g → Nonempty (FGRecursive (HNNEmb.Ext g))

/-- Free groups are torsion-free; this one is Mathlib's. -/
theorem isPowerTorsionFree_freeGroup {α : Type} :
    IsPowerTorsionFree (FreeGroup α) :=
  IsPowerTorsionFree.of_isMulTorsionFree

/-- **The extension is torsion-free when the group is.**  No hypothesis: both
permanence theorems are proved in this repository. -/
theorem torsionFree_ext {A : Type} [Group A] (g : ℕ → A)
    (hA : IsPowerTorsionFree A) : IsPowerTorsionFree (HNNEmb.Ext g) :=
  HNNBritton.isPowerTorsionFree_hnn (HNNEmb.psi g)
    (isPowerTorsionFree_coprod hA isPowerTorsionFree_freeGroup)

/-- A group with a countable generating family is countable. -/
theorem countable_of_recursivePresentation {A : Type} [Group A]
    (p : RecursivePresentation A) : Countable A := by
  have hsurj : Function.Surjective (fun w : RawWord => evalRaw p.gen w) := by
    intro x
    exact (spans_iff_forall_exists_evalRaw p.gen).mp p.spans x
  exact hsurj.countable

/-- **The effectivity clause gives the bridge.**  The torsion clause is
supplied by `torsionFree_ext`, which is unconditional. -/
theorem countableToFG_of_input (h : BridgeRecursive) : CountableToFG where
  bridge := by
    intro A _ p htf
    classical
    haveI : Countable A := countable_of_recursivePresentation p
    haveI : Nonempty A := ⟨1⟩
    obtain ⟨g, hg⟩ := exists_surjective_nat A
    obtain ⟨q⟩ := h.recursive A g p hg
    exact ⟨{ Carrier := HNNEmb.Ext g
             recursive := q
             torsionFree := torsionFree_ext g htf
             emb := HNNEmb.embA g
             emb_injective := HNNEmb.embA_injective g }⟩

end Higman
end GroupApproximation
