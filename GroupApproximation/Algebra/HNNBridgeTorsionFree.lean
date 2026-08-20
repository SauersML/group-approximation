import GroupApproximation.Algebra.CoprodICyclicReduction
import GroupApproximation.GroupTheory.HNNBrittonCyclic

/-!
# The torsion clause of the Higman--Neumann--Neumann bridge

`Higman.CountableToFG` --- the bridge that embeds a countable recursively
presented torsion-free group in a *finitely generated* one --- is built as an
HNN extension of `A ∗ F₂`.  It has three clauses: the embedding, recursive
presentability, and torsion-freeness.  **The torsion clause is now free.**

Two theorems combine, and each was the harder half of its own file:

* `Algebra.CoprodICyclicReduction.isPowerTorsionFree_coprodI` --- a free
  product of torsion-free groups is torsion-free, proved by cyclic reduction
  against Mathlib's head-only normal form;
* `HNNBritton.isPowerTorsionFree_hnn` --- an HNN extension of a torsion-free
  group is torsion-free, over any associated pair, already proved in this
  repository from Britton's lemma.

Neither depends on the other, and their composite is exactly the shape the
bridge needs: an HNN extension of a free product.  Nothing here is new
mathematics; the point is that the clause is now discharged rather than
assumed, so what `CountableToFG` still owes is the *construction* --- the two
free bases and the isomorphism between the associated subgroups --- and the
recursive-presentability clause.
-/

namespace GroupApproximation
namespace HNNBridgeTorsionFree

open Monoid Monoid.CoprodI

variable {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, Group (M i)]
  [∀ i, DecidableEq (M i)]

/-- **The torsion clause of the bridge.**  An HNN extension of a free product
of torsion-free groups is torsion-free, over any associated pair. -/
theorem isPowerTorsionFree_hnnExtension_coprodI
    (hfac : ∀ i, IsPowerTorsionFree (M i))
    {A B : Subgroup (CoprodI M)} (φ : A ≃* B) :
    IsPowerTorsionFree (HNNExtension (CoprodI M) A B φ) :=
  HNNBritton.isPowerTorsionFree_hnn φ
    (CoprodICyclicReduction.isPowerTorsionFree_coprodI hfac)

/-- The same, iterated: a tower of HNN extensions over a free product of
torsion-free groups stays torsion-free.  Stated for one further step, which is
all the bridge uses. -/
theorem isPowerTorsionFree_hnnExtension_two
    (hfac : ∀ i, IsPowerTorsionFree (M i))
    {A B : Subgroup (CoprodI M)} (φ : A ≃* B)
    {C D : Subgroup (HNNExtension (CoprodI M) A B φ)} (ψ : C ≃* D) :
    IsPowerTorsionFree (HNNExtension (HNNExtension (CoprodI M) A B φ) C D ψ) :=
  HNNBritton.isPowerTorsionFree_hnn ψ
    (isPowerTorsionFree_hnnExtension_coprodI hfac φ)

end HNNBridgeTorsionFree
end GroupApproximation
