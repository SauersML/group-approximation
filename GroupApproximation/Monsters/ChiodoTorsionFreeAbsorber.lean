import GroupApproximation.Monsters.UniversalFinitelyPresentedGroup
import GroupApproximation.Algebra.TorsionFreeQuotient
import Mathlib.Data.DFinsupp.Encodable

/-!
# A countable torsion-free group absorbing every finitely presented
torsion-free group, indexed by *all* presentations

This is Chiodo's construction (arXiv:1107.1489v4, proof of Theorem 3.9) with
his free product replaced by a restricted direct product, and it is here to
remove one specific obstruction.

## The obstruction it removes

`Monsters.UniversalFinitelyPresentedTorsionFreeGroup` already builds a
countable torsion-free group absorbing every finitely presented torsion-free
group.  It does it by *filtering*: the index type is

    {c : FinitePresentationCode // IsPowerTorsionFree (CodedPresentedGroup c)},

the presentation codes whose group happens to be torsion-free.  That group is
countable and torsion-free and absorbs everything, and it is useless as an
input to Higman's embedding theorem, because Higman's theorem is about
*recursively presented* groups and this one is not recursively presented:
torsion-freeness is a Markov property, so by Adian--Rabin the index set is
undecidable, and a presentation whose relator set is indexed by an
undecidable set is not a recursive presentation.  The proof ledger records
that as the reason `KC.21`'s first input could not be reduced to Higman by
this repository's own payload.

The filtering is not necessary.  Take the restricted direct product over
**every** presentation code --- the full, manifestly decidable index type ---
and then pass to the universal torsion-free quotient of the result:

    A := (⨁_{c : FinitePresentationCode} G_c)^tf .

The direct sum is torsion-free nowhere near everywhere, and `A` is
torsion-free for free, by `Algebra.TorsionFreeQuotient`.  What has to be
checked is that the torsion of the other coordinates does not damage the
coordinates one cares about, and that is the retraction principle: a
coordinate of a direct product is a *retract*, and a torsion-free retract
survives the passage to the torsion-free quotient
(`Chiodo.injective_of_retraction`).  The evaluation homomorphism
`codedEval c` is the retraction, and `codedEval_codedOf` is the only fact
about the direct product this file needs.

So `A` absorbs every finitely presented torsion-free group, is countable, is
torsion-free, and is presented on a generating set indexed by all of
`FinitePresentationCode` --- with the passage to `^tf` as the only
non-syntactic step, which is exactly the step Chiodo's Proposition 3.8 makes
effective.  `Sofic.ChiodoUniversalHost` says what remains owed.

## What is *not* claimed here

Nothing in this file says `A` is recursively presented.  That is a statement
about presentations and computability, it needs Chiodo's Proposition 3.8, and
this repository's computability layer does not yet have the notion.  What is
claimed, and proved, is that the obstruction which blocked the *filtered*
payload is absent here: the index type is the whole code type, and the only
quotient taken is by the torsion-free radical.
-/

namespace GroupApproximation
namespace Monsters

open GroupApproximation.Chiodo

/-! ## 1.  The restricted direct product of all coded groups -/

instance codedPresentedGroup_additive_countable (c : FinitePresentationCode) :
    Countable (Additive (CodedPresentedGroup c)) :=
  Countable.of_equiv (CodedPresentedGroup c) Additive.ofMul

/-- The restricted direct product of the groups of *all* finite presentation
codes.  No filtering: coordinates with torsion are kept. -/
def CodedDirectSum : Type :=
  Multiplicative
    (Π₀ c : FinitePresentationCode, Additive (CodedPresentedGroup c))

instance codedDirectSum_group : Group CodedDirectSum := by
  unfold CodedDirectSum
  infer_instance

instance codedDirectSum_countable : Countable CodedDirectSum := by
  unfold CodedDirectSum
  exact Countable.of_equiv
    (Π₀ c : FinitePresentationCode, Additive (CodedPresentedGroup c))
    Multiplicative.ofAdd

/-- The inclusion of one coordinate. -/
noncomputable def codedOf (c : FinitePresentationCode) :
    CodedPresentedGroup c →* CodedDirectSum := by
  classical
  exact
    { toFun := fun x ↦
        Multiplicative.ofAdd (DFinsupp.single c (Additive.ofMul x))
      map_one' := by
        change Multiplicative.ofAdd
            (DFinsupp.single c (Additive.ofMul (1 : CodedPresentedGroup c))) =
          Multiplicative.ofAdd
            (0 : (Π₀ i : FinitePresentationCode,
              Additive (CodedPresentedGroup i)))
        apply Multiplicative.ofAdd.injective
        simp
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd
            (DFinsupp.single c (Additive.ofMul (x * y))) =
          Multiplicative.ofAdd
            ((DFinsupp.single c (Additive.ofMul x) :
                (Π₀ i : FinitePresentationCode,
                  Additive (CodedPresentedGroup i))) +
              (DFinsupp.single c (Additive.ofMul y) :
                (Π₀ i : FinitePresentationCode,
                  Additive (CodedPresentedGroup i))))
        exact congrArg Multiplicative.ofAdd
          ((DFinsupp.single_add
            (β := fun i : FinitePresentationCode ↦
              Additive (CodedPresentedGroup i)) c (Additive.ofMul x)
            (Additive.ofMul y))) }

/-- Evaluation at one coordinate.  This is the retraction the construction
runs on. -/
noncomputable def codedEval (c : FinitePresentationCode) :
    CodedDirectSum →* CodedPresentedGroup c where
  toFun q := Additive.toMul (Multiplicative.toAdd q c)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The retraction identity.**  Evaluating a coordinate inclusion at its own
coordinate returns the element.  Everything this file proves about
`CodedDirectSum` goes through this one equation. -/
theorem codedEval_codedOf (c : FinitePresentationCode)
    (x : CodedPresentedGroup c) : codedEval c (codedOf c x) = x := by
  classical
  have h : codedEval c (codedOf c x)
      = Additive.toMul (Multiplicative.toAdd (codedOf c x) c) := rfl
  rw [h]
  simp [codedOf]

theorem codedOf_injective (c : FinitePresentationCode) :
    Function.Injective (codedOf c) := by
  intro x y hxy
  have h := congrArg (codedEval c) hxy
  rwa [codedEval_codedOf, codedEval_codedOf] at h

/-! ## 2.  The absorber -/

/-- **The absorber**: the universal torsion-free quotient of the restricted
direct product of all coded finitely presented groups. -/
abbrev ChiodoAbsorber : Type := TorsionFreeQuotient CodedDirectSum

/-- The absorber is torsion-free.  This is Chiodo's Corollary 3.4 and nothing
else; no property of the coordinates is used. -/
theorem chiodoAbsorber_torsionFree : IsPowerTorsionFree ChiodoAbsorber :=
  isPowerTorsionFree_torsionFreeQuotient

instance chiodoAbsorber_countable : Countable ChiodoAbsorber :=
  Function.Surjective.countable toTorsionFreeQuotient_surjective

/-- The map placing one coordinate into the absorber. -/
noncomputable def chiodoEmb (c : FinitePresentationCode) :
    CodedPresentedGroup c →* ChiodoAbsorber :=
  (toTorsionFreeQuotient CodedDirectSum).comp (codedOf c)

/-- **A torsion-free coordinate survives the quotient.**  The other
coordinates may be as full of torsion as they like: the retraction
`codedEval c` maps to a torsion-free group, so it kills the torsion-free
radical, and therefore the radical meets this coordinate trivially. -/
theorem chiodoEmb_injective (c : FinitePresentationCode)
    (hc : IsPowerTorsionFree (CodedPresentedGroup c)) :
    Function.Injective (chiodoEmb c) := by
  unfold chiodoEmb
  exact injective_of_retraction hc (codedOf c) (codedEval c)
    (codedEval_codedOf c)

/-- **The absorbing property.**  Every finitely presented torsion-free group
embeds in the absorber. -/
theorem embeds_chiodoAbsorber (Q : Type) [Group Q] [Group.IsFinitelyPresented Q]
    (hQ : IsPowerTorsionFree Q) :
    ∃ f : Q →* ChiodoAbsorber, Function.Injective f := by
  obtain ⟨c, ⟨e⟩⟩ := exists_mulEquiv_codedPresentedGroup Q
  have hc : IsPowerTorsionFree (CodedPresentedGroup c) :=
    IsPowerTorsionFree.comap hQ e.symm.toMonoidHom e.symm.injective
  refine ⟨(chiodoEmb c).comp e.toMonoidHom, ?_⟩
  exact (chiodoEmb_injective c hc).comp e.injective

/-- **The absorber is nontrivial.**  `Multiplicative ℤ` is finitely presented
and torsion-free, so it embeds; in particular the passage to the torsion-free
quotient did not collapse the direct sum.  Recorded because every consumer of
a universal group needs a nonidentity element and none of them says where it
comes from. -/
theorem exists_ne_one_chiodoAbsorber : ∃ a : ChiodoAbsorber, a ≠ 1 := by
  obtain ⟨f, hf⟩ :=
    embeds_chiodoAbsorber (Multiplicative ℤ)
      IsPowerTorsionFree.of_isMulTorsionFree
  refine ⟨f (Multiplicative.ofAdd (1 : ℤ)), ?_⟩
  intro hone
  have hx : (Multiplicative.ofAdd (1 : ℤ)) = 1 :=
    hf (hone.trans (map_one f).symm)
  have hz := congrArg (fun x : Multiplicative ℤ ↦ Multiplicative.toAdd x) hx
  change (1 : ℤ) = 0 at hz
  exact one_ne_zero hz

/-- The absorbing property in the shape the downstream reduction consumes:
any group containing the absorber contains every finitely presented
torsion-free group. -/
theorem universal_of_embedding_chiodoAbsorber {P : Type} [Group P]
    (g : ChiodoAbsorber →* P) (hg : Function.Injective g) :
    ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* P, Function.Injective f := by
  intro Q _ _ hQ
  obtain ⟨f, hf⟩ := embeds_chiodoAbsorber Q hQ
  exact ⟨g.comp f, hg.comp hf⟩

end Monsters
end GroupApproximation
