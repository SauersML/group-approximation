import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Algebra.TorsionFreeQuotient
import Mathlib.Data.DFinsupp.Encodable

/-!
# The absorber over the *computable* coding of finite presentations

`Monsters.ChiodoTorsionFreeAbsorber` builds the absorbing group over
`Monsters.FinitePresentationCode`, which is `Σ n, Finset (FreeGroup (Fin n))`.
That type is countable, which is all the group theory needs, and it is **not**
a computable coding: `Finset (FreeGroup (Fin n))` carries no `Primcodable`
instance, so no statement of the form "the relator set of this presentation is
recursively enumerable" can even be written over it.

`Computability.PresentationCodes` fixes the computable coding this repository
already uses for its Adian--Rabin work: `PresentationCode = ℕ × List (List (ℕ
× Bool))`, which *is* `Primcodable`, whose `Carrier c` is finitely presented,
and which is adequate --- `exists_code_mulEquiv` names every finitely
presented group.

This file runs the same construction over that coding.  The mathematics is
identical, the retraction principle again doing all the work; what changes is
that the index type is now one over which recursive enumerability is a
meaningful predicate, which is what Chiodo's Proposition 3.8 --- input (B) of
`Higman.Program` --- has to be stated over.

Both absorbers are kept.  The one over `FinitePresentationCode` is what
`Sofic.ChiodoUniversalHost` consumes and is the shortest route to the
universality statement; this one is the route to the *computability*
statement.  `absorbs_recursiveAbsorber` and
`Monsters.embeds_chiodoAbsorber` are the same theorem over different index
sets, and neither is derived from the other.
-/

namespace GroupApproximation
namespace Monsters

open GroupApproximation.Chiodo
open GroupApproximation.PresentationCodes

/-- The index type is a computable coding: this is the whole point of the
file. -/
example : Primcodable PresentationCode := inferInstance

instance recursiveCarrier_countable (c : PresentationCode) :
    Countable (Carrier c) := by
  change Countable
    (Quotient (QuotientGroup.leftRel
      (Subgroup.normalClosure
        ((relatorFinset c : Finset (FreeGroup (Fin (genCount c)))) :
          Set (FreeGroup (Fin (genCount c)))))))
  infer_instance

instance recursiveCarrier_additive_countable (c : PresentationCode) :
    Countable (Additive (Carrier c)) :=
  Countable.of_equiv (Carrier c) Additive.ofMul

/-- The restricted direct product of the groups of *all* computable
presentation codes. -/
def RecursiveDirectSum : Type :=
  Multiplicative (Π₀ c : PresentationCode, Additive (Carrier c))

instance recursiveDirectSum_group : Group RecursiveDirectSum := by
  unfold RecursiveDirectSum
  infer_instance

instance recursiveDirectSum_countable : Countable RecursiveDirectSum := by
  unfold RecursiveDirectSum
  exact Countable.of_equiv
    (Π₀ c : PresentationCode, Additive (Carrier c)) Multiplicative.ofAdd

/-- The inclusion of one coordinate. -/
noncomputable def recursiveOf (c : PresentationCode) :
    Carrier c →* RecursiveDirectSum := by
  classical
  exact
    { toFun := fun x ↦
        Multiplicative.ofAdd (DFinsupp.single c (Additive.ofMul x))
      map_one' := by
        change Multiplicative.ofAdd
            (DFinsupp.single c (Additive.ofMul (1 : Carrier c))) =
          Multiplicative.ofAdd
            (0 : (Π₀ i : PresentationCode, Additive (Carrier i)))
        apply Multiplicative.ofAdd.injective
        simp
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd
            (DFinsupp.single c (Additive.ofMul (x * y))) =
          Multiplicative.ofAdd
            ((DFinsupp.single c (Additive.ofMul x) :
                (Π₀ i : PresentationCode, Additive (Carrier i))) +
              (DFinsupp.single c (Additive.ofMul y) :
                (Π₀ i : PresentationCode, Additive (Carrier i))))
        exact congrArg Multiplicative.ofAdd
          ((DFinsupp.single_add
            (β := fun i : PresentationCode ↦ Additive (Carrier i)) c
            (Additive.ofMul x) (Additive.ofMul y))) }

/-- Evaluation at one coordinate: the retraction. -/
noncomputable def recursiveEval (c : PresentationCode) :
    RecursiveDirectSum →* Carrier c where
  toFun q := Additive.toMul (Multiplicative.toAdd q c)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem recursiveEval_recursiveOf (c : PresentationCode) (x : Carrier c) :
    recursiveEval c (recursiveOf c x) = x := by
  classical
  have h : recursiveEval c (recursiveOf c x)
      = Additive.toMul (Multiplicative.toAdd (recursiveOf c x) c) := rfl
  rw [h]
  simp [recursiveOf]

/-- **The absorber over the computable coding.** -/
abbrev RecursiveAbsorber : Type := TorsionFreeQuotient RecursiveDirectSum

theorem recursiveAbsorber_torsionFree : IsPowerTorsionFree RecursiveAbsorber :=
  isPowerTorsionFree_torsionFreeQuotient

instance recursiveAbsorber_countable : Countable RecursiveAbsorber :=
  Function.Surjective.countable toTorsionFreeQuotient_surjective

/-- The map placing one coordinate into the absorber. -/
noncomputable def recursiveEmb (c : PresentationCode) :
    Carrier c →* RecursiveAbsorber :=
  (toTorsionFreeQuotient RecursiveDirectSum).comp (recursiveOf c)

theorem recursiveEmb_injective (c : PresentationCode)
    (hc : IsPowerTorsionFree (Carrier c)) :
    Function.Injective (recursiveEmb c) := by
  unfold recursiveEmb
  exact injective_of_retraction hc (recursiveOf c) (recursiveEval c)
    (recursiveEval_recursiveOf c)

/-- **The absorbing property, over the computable coding.** -/
theorem absorbs_recursiveAbsorber (Q : Type) [Group Q]
    [Group.IsFinitelyPresented Q] (hQ : IsPowerTorsionFree Q) :
    ∃ f : Q →* RecursiveAbsorber, Function.Injective f := by
  obtain ⟨c, ⟨e⟩⟩ := exists_code_mulEquiv Q
  have hc : IsPowerTorsionFree (Carrier c) :=
    IsPowerTorsionFree.comap hQ e.toMonoidHom e.injective
  refine ⟨(recursiveEmb c).comp e.symm.toMonoidHom, ?_⟩
  exact (recursiveEmb_injective c hc).comp e.symm.injective

/-- The universality formula, off any embedding of this absorber. -/
theorem universal_of_embedding_recursiveAbsorber {P : Type} [Group P]
    (g : RecursiveAbsorber →* P) (hg : Function.Injective g) :
    ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* P, Function.Injective f := by
  intro Q _ _ hQ
  obtain ⟨f, hf⟩ := absorbs_recursiveAbsorber Q hQ
  exact ⟨g.comp f, hg.comp hf⟩

/-- The absorber is nontrivial: `Multiplicative ℤ` is finitely presented and
torsion-free, so it embeds. -/
theorem exists_ne_one_recursiveAbsorber : ∃ a : RecursiveAbsorber, a ≠ 1 := by
  obtain ⟨f, hf⟩ :=
    absorbs_recursiveAbsorber (Multiplicative ℤ)
      IsPowerTorsionFree.of_isMulTorsionFree
  refine ⟨f (Multiplicative.ofAdd (1 : ℤ)), ?_⟩
  intro hone
  have hx : (Multiplicative.ofAdd (1 : ℤ)) = 1 :=
    hf (hone.trans (map_one f).symm)
  have hz := congrArg (fun x : Multiplicative ℤ ↦ Multiplicative.toAdd x) hx
  change (1 : ℤ) = 0 at hz
  exact one_ne_zero hz

end Monsters
end GroupApproximation
