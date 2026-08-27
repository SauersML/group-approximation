import GroupApproximation.Computability.RabinConstruction
import GroupApproximation.Computability.OperatorMFMarkovWitness

/-!
# The positive clause of the Adian--Rabin biconditional, for operator-MF

`Computability.RabinConstruction` builds the finite presentation `K(w)` of the
Adian--Rabin construction and proves that it presents the trivial group when the
source word `w` is trivial.  This file docks that collapse onto the
manuscript's Markov property.

The manuscript's description of the reduction (see the anchors recorded in
`Computability.RabinConstruction`) has two clauses:

> ... a finite presentation whose group is trivial --- hence MF --- when `w=1`,
> and contains `E` --- hence non-MF, by subgroup heredity --- when `w≠1`.

**The first clause is proved here, unconditionally**, as
`rabin_finitelyPresented_and_isOperatorMF_of_word_eq_one`: the constructed group
is finitely presented, and it is operator-MF because it is trivial, hence
finite, and finite groups are operator-MF
(`isOperatorMF_of_finite_standard`).

**The second clause is not proved anywhere in this repository.**  What exists is
its *consequence* given an embedding: `OperatorMFMarkovWitness`
`chosen_forbidden_subgroup` already says that no injective homomorphism from the
repository's finitely presented non-MF group into an operator-MF group exists,
so an embedding `E ↪ K(w)` would immediately give `¬ IsOperatorMF (K(w))`.  That
theorem is already stated and proved there and is deliberately *not* restated
here specialised to `K(w)`: restating it would invite the misreading that the
embedding itself has been supplied.  It has not.  The missing input is the
injection, and the roadmap for producing it (steps E1--E7) is in the module
docstring of `Computability.RabinConstruction`.

Nothing in this file or in `Computability.RabinConstruction` is conditional.
The only hypothesis appearing anywhere is `w = 1 in Γ`, which is the *antecedent
of the biconditional being proved*, not an imported theorem: the biconditional
`K(w) has P ↔ w = 1 in Γ` is a statement about an arbitrary source group and an
arbitrary word, and no undecidability input enters it.  The honest status of its
two directions, and of the two computability inputs that sit above it:

| clause | status |
|---|---|
| `w = 1 ⟹ K(w)` finitely presented and MF | **proved here** |
| `w ≠ 1 ⟹ E ↪ K(w)` | **missing** (needs Britton normal forms, ~2500 lines) |
| `E ↪ K(w) ⟹ ¬ MF (K(w))` | already proved, `OperatorMFMarkovWitness` |
| the reduction is computable on codes | missing (encoding layer) |
| the source word problem is undecidable | missing (Novikov--Boone) |
-/

namespace GroupApproximation
namespace RabinConstruction

variable {n : ℕ} (R : Finset (FreeGroup (Fin n))) (w : FreeGroup (Fin n))

/-- **The positive clause, in MF form.**  When the source word `w` is trivial,
the Adian--Rabin group `K(w)` is operator-MF, because the collapse makes it
trivial and finite groups are operator-MF.

This is unconditional: `rabin_trivial_of_word_eq_one` carries no hypothesis
encoding an unformalized theorem, and `isOperatorMF_of_finite_standard` is a
theorem of this repository. -/
theorem rabin_isOperatorMF_of_word_eq_one
    (hw : PresentedGroup.mk ((R : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))) w = 1) :
    IsOperatorMF (RabinGroup R w) := by
  haveI : Subsingleton (RabinGroup R w) := rabin_trivial_of_word_eq_one R w hw
  haveI : Finite (RabinGroup R w) := Finite.of_subsingleton
  exact isOperatorMF_of_finite_standard (RabinGroup R w)

/-- **The manuscript's positive clause verbatim**: the construction outputs a
*finite presentation* whose group is trivial --- hence MF --- when `w = 1`. -/
theorem rabin_finitelyPresented_and_isOperatorMF_of_word_eq_one
    (hw : PresentedGroup.mk ((R : Finset (FreeGroup (Fin n))) :
      Set (FreeGroup (Fin n))) w = 1) :
    Group.IsFinitelyPresented (RabinGroup R w) ∧ IsOperatorMF (RabinGroup R w) :=
  ⟨rabin_isFinitelyPresented R w, rabin_isOperatorMF_of_word_eq_one R w hw⟩

end RabinConstruction
end GroupApproximation
