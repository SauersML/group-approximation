import GroupApproximation.Analysis.TikuisisWhiteWinter
import GroupApproximation.Analysis.DadarlatEilers
import GroupApproximation.Analysis.KirchbergRordamOrderZeroLift

/-!
# Tikuisis--White--Winter, over a defined UCT

`Analysis.TikuisisWhiteWinter` states the theorem

> every faithful trace on a separable nuclear C⋆-algebra satisfying the UCT is
> quasidiagonal

(Tikuisis, White, Winter, *Quasidiagonality of nuclear C⋆-algebras*, Ann. of
Math. (2) **185** (2017), 229--284, Theorem A) with the UCT as an
**uninterpreted predicate parameter** `UCT : Type u → Prop`, because at the
time nothing in this development could define it.  Its docstring says so
explicitly: "`KK`-theory does not exist in this development or in mathlib, so
no honest definition can be given here."

That is what this file changes.  With `Analysis.KKTheoryKasparov` and
`Analysis.UniversalCoefficientTheorem` in place the UCT is a **definition** ---
`KK`-equivalence to a commutative C⋆-algebra, Rosenberg--Schochet's
characterization of the bootstrap class --- and the theorem can be stated with
it.  Three things follow, and they are what this file contains.

1. `TikuisisWhiteWinterTheorem` --- the theorem, stated at the defined UCT and
   at bundled separable algebras, so that separability is carried by the
   object rather than by a side hypothesis.
2. `tikuisisWhiteWinterInput_of_theorem` --- the new statement **implies** the
   old parameterized input, at the predicate `uctPredicate`.  So nothing
   already proved from the old input is lost, and the parameter is no longer
   free: it is pinned to a definition.
3. The group route, re-proved at the defined UCT
   (`isQuasidiagonalTrace_canonicalReduced`, `isOperatorMF_of_isAmenable`),
   with Tu's theorem now stated as a `SatisfiesUCT` obligation about a bundled
   algebra rather than as an assertion about an abstract predicate that
   nothing constrains.

## What remains irreducible, stated once and plainly

`TikuisisWhiteWinterTheorem` is a structure and **no unconditional inhabitant
is constructed here or anywhere in this development**.  It is, however, no
longer *assumed*: `Analysis.TikuisisWhiteWinterDerivation` derives it, in two
independent ways, from strictly finer named inputs --- from the corona form of
the argument (`CoronaEmbeddingInput`, with the translation back to asymptotic
language proved in `Analysis.QuasidiagonalCoronaCriterion`), and from
Connes--Haagerup together with the local, amenable-trace form of the Annals
theorem.  So no theorem in this development carries a
`TikuisisWhiteWinterTheorem` binder that could not be replaced by a finer one.

Its proof, in the Annals paper, runs through:

* the Kirchberg--Rørdam structure theory of the corona `∏ Mₖ / ⊕ Mₖ` ---
  countable saturation is *proved* here, unconditionally, from Kirchberg's
  `ε`-test (`Analysis.KirchbergRordamEpsilonTest`,
  `Analysis.KirchbergRordamCorona`); the order-zero lifting theorem is
  **not**, and is the input `OrderZero.CoronaOrderZeroLiftInput`;
* completely positive contractive **order-zero maps** --- the constructive
  half of Winter--Zacharias is *proved* here
  (`OrderZero.OrderZeroSupport.isOrderZero`), the structure half is the input
  `OrderZero.WinterZachariasInput`;
* `KK`-theory and the UCT --- assumed as `KK.KasparovTheory`, with all the
  consequences the route needs proved from its axioms;
* the **Dadarlat--Eilers stable uniqueness theorem** --- assumed as
  `KK.DadarlatEilersInput`, with the direct-sum machinery it is stated over
  proved (`KK.Amplifier`);
* the tracial machinery of Ozawa--Rørdam--Sato, which has no counterpart here
  at all.

So the honest summary is: the *reduction* is formalized, the *statement* is now
expressed in defined terms, and the theorem is *derived* from the vocabulary of
its own proof rather than postulated.  What is finally assumed is the Annals
argument in one of its two finer forms, plus Kasparov; the rest of the list is
either proved here or stated but unused.  This is the same discipline
`Analysis.TikuisisWhiteWinterCore` applies to the amenability seam, carried
two layers further down.

**Nothing below concludes an input structure from premise-free hypotheses**;
every conclusion is pointwise, with head `IsQuasidiagonalTrace` or
`IsOperatorMF`, for the reason `Analysis.AmenableMFInput` records.
-/

namespace GroupApproximation
namespace QuasidiagonalMF

open ReducedGroupCStarTrace
open KK

noncomputable section

universe u

/-! ## The algebras of the route, as objects of the Kasparov category -/

/-- The reduced C⋆-algebra of a countable group, as a bundled separable
C⋆-algebra.  Separability is `reducedGroupCStar_separableSpace`, a theorem of
this development, so this object costs nothing beyond countability of `G`. -/
def reducedObject (G : Type u) [Group G] [Countable G] : SepCStarAlgebra.{u} where
  carrier := ReducedGroupCStar G
  separable := reducedGroupCStar_separableSpace G

/-! ## The theorem, at the defined UCT -/

/-- **The Tikuisis--White--Winter theorem, stated over a `KasparovTheory`.**

Every faithful trace on a nuclear C⋆-algebra in the bootstrap class is
quasidiagonal.  Separability is carried by the object `S`, nuclearity is the
completely positive approximation property, and the UCT is
`KasparovTheory.SatisfiesUCT` --- a *definition*, not a parameter.

**Not assumed anywhere.**  `Analysis.TikuisisWhiteWinterDerivation` produces
this structure from finer inputs, in two independent ways, so a theorem
consuming it consumes something derivable rather than something postulated.
No *unconditional* inhabitant is constructed --- see the module docstring for
the list of what that would need and which parts of the list this development
supplies. -/
structure TikuisisWhiteWinterTheorem (T : KasparovTheory.{u}) : Prop where
  /-- A faithful trace on a nuclear bootstrap-class algebra is
  quasidiagonal. -/
  quasidiagonal : ∀ S : SepCStarAlgebra.{u},
    CStarExactness.IsNuclearCStarAlgebra S →
      T.SatisfiesUCT S →
        ∀ τ : FaithfulTracialState S,
          Quasidiagonal.IsQuasidiagonalTrace (fun a : S => τ a)

/-! ## Pinning the old parameter -/

/-- **The UCT as a predicate on types**, which is the shape
`Analysis.TikuisisWhiteWinter` can consume.

A `Type u → Prop` cannot see a C⋆-structure, so the predicate quantifies over
the structures the type may carry: `uctPredicate T A` says that *whichever*
separable C⋆-structure `A` is given, the resulting algebra is in the bootstrap
class.  In every application the type carries one structure of interest and
the quantifier is vacuous beyond it.

The universal form is chosen deliberately, and it is the direction that costs
nothing here: it makes `uctPredicate` *harder* to satisfy, hence
`TikuisisWhiteWinterInput (uctPredicate T)` *easier*, which is what
`tikuisisWhiteWinterInput_of_theorem` has to produce.  A user supplying Tu's
theorem in this shape carries the corresponding extra burden, which is why the
group route below does **not** go through this predicate at all --- it states
Tu's input directly at the bundled algebra. -/
def uctPredicate (T : KasparovTheory.{u}) (A : Type u) : Prop :=
  ∀ (inst : CStarAlgebra A) (sep : TopologicalSpace.SeparableSpace A),
    T.SatisfiesUCT (@SepCStarAlgebra.mk A inst sep)

/-- **The defined statement implies the parameterized one.**

Everything `Analysis.TikuisisWhiteWinter` proves from
`TikuisisWhiteWinterInput` is therefore available from
`TikuisisWhiteWinterTheorem`, with the UCT parameter instantiated by a
definition instead of left free. -/
theorem tikuisisWhiteWinterInput_of_theorem {T : KasparovTheory.{u}}
    (h : TikuisisWhiteWinterTheorem T) :
    TikuisisWhiteWinterInput (uctPredicate T) where
  quasidiagonalTrace := by
    intro A instA hsep hnuc huct τ
    exact h.quasidiagonal (@SepCStarAlgebra.mk A instA hsep) hnuc
      (huct instA hsep) τ

/-! ## The group route, at the defined UCT -/

/-- **The first premise of the printed factorization, over defined
hypotheses.**

Granting Tikuisis--White--Winter, Lance's nuclearity theorem and Tu's UCT
theorem, the canonical trace of the reduced C⋆-algebra of a countable amenable
group is quasidiagonal.

Compare `isQuasidiagonalTrace_canonicalReduced_of_amenable`: there, `UCT` is an
abstract predicate and `AmenableUCTInput` asserts something about it that
nothing else constrains --- the two occurrences of the parameter could be
matched by *any* predicate, including the constantly-true one, which is
exactly why that formulation cannot be audited.  Here Tu's input is an
obligation about `SatisfiesUCT`, a definition, at a specific bundled
algebra. -/
theorem isQuasidiagonalTrace_canonicalReduced {T : KasparovTheory.{u}}
    (tww : TikuisisWhiteWinterTheorem T) (lance : AmenableNuclearInput.{u})
    (tu : ∀ (H : Type u) (_ : Group H) (_ : Countable H),
      Amenability.IsAmenable H → T.SatisfiesUCT (reducedObject H))
    (G : Type u) [Group G] [Countable G] (hA : Amenability.IsAmenable G) :
    Quasidiagonal.IsQuasidiagonalTrace
      (fun x : ReducedGroupCStar G => canonicalFaithfulTracialState G x) :=
  tww.quasidiagonal (reducedObject G) (lance.nuclear G inferInstance hA)
    (tu G inferInstance inferInstance hA) (canonicalFaithfulTracialState G)

/-- **`INT.11`, group by group, over the inputs it actually rests on** --- the
same statement as `isOperatorMF_of_isAmenable_of_tww`, with the UCT parameter
replaced by the definition.

Every countable amenable group is operator-MF, granting: the ucp facts, the
Tikuisis--White--Winter theorem at the defined UCT, Lance's theorem, and Tu's
theorem.  The reduction half --- quasidiagonal canonical trace implies
operator-MF --- is a theorem of this development, not an input; see
`isOperatorMF_of_isQuasidiagonalCanonicalTrace`.

**The conclusion is `IsOperatorMF G` and not `AmenableMFInput`,
deliberately.** -/
theorem isOperatorMF_of_isAmenable (hucp : Quasidiagonal.UCPContractive.{u})
    {T : KasparovTheory.{u}} (tww : TikuisisWhiteWinterTheorem T)
    (lance : AmenableNuclearInput.{u})
    (tu : ∀ (H : Type u) (_ : Group H) (_ : Countable H),
      Amenability.IsAmenable H → T.SatisfiesUCT (reducedObject H))
    (G : Type u) [Group G] [Countable G] (hA : Amenability.IsAmenable G) :
    IsOperatorMF G :=
  isOperatorMF_of_isQuasidiagonalCanonicalTrace hucp G
    (isQuasidiagonalTrace_canonicalReduced tww lance tu G hA)

/-- **The contrapositive**, which is the shape `sec:consequences` uses. -/
theorem not_isAmenable_of_not_isOperatorMF
    (hucp : Quasidiagonal.UCPContractive.{u})
    {T : KasparovTheory.{u}} (tww : TikuisisWhiteWinterTheorem T)
    (lance : AmenableNuclearInput.{u})
    (tu : ∀ (H : Type u) (_ : Group H) (_ : Countable H),
      Amenability.IsAmenable H → T.SatisfiesUCT (reducedObject H))
    (G : Type u) [Group G] [Countable G] (hMF : ¬ IsOperatorMF G) :
    ¬ Amenability.IsAmenable G :=
  fun hA => hMF (isOperatorMF_of_isAmenable hucp tww lance tu G hA)

/-! ## The irreducible core, named

The five inputs of the route, in one place, so that a reader can count them
without reading the file:

| input | owner | where |
|---|---|---|
| `CoronaEmbeddingInput`, **or** `NuclearAmenableTraceInput` + `TikuisisWhiteWinterCoreInput` | Tikuisis--White--Winter 2017 (and Connes--Haagerup) | `Analysis.TikuisisWhiteWinterDerivation`, `Analysis.TikuisisWhiteWinterCore` |
| `KK.KasparovTheory` | Kasparov 1980--88 | `Analysis.KKTheoryKasparov` |
| `KK.DadarlatEilersInput` | Dadarlat--Eilers 2002 | `Analysis.DadarlatEilers` |
| `OrderZero.WinterZachariasInput` | Winter--Zacharias 2009 | `Analysis.KirchbergRordamOrderZeroLift` |
| `OrderZero.CoronaOrderZeroLiftInput` | Kirchberg--Rørdam 2014 | `Analysis.KirchbergRordamOrderZeroLift` |

The last four are *not* consumed by anything above: the group route uses only
the Annals input --- in whichever of its two finer forms --- plus Lance and
Tu.  They are stated because they are the theorems
`TikuisisWhiteWinterTheorem`'s own proof consumes, and stating them is what
makes the claim "this is where the irreducibility sits" checkable rather than
rhetorical.  A future formalization of TWW would produce an inhabitant of
`TikuisisWhiteWinterTheorem` from those four together with the material this
development proves unconditionally: countable saturation of the corona, the
supported picture of order-zero maps, the `KK`-consequences of the Kasparov
axioms, and the local-to-global step already in
`Analysis.QuasidiagonalTraceLocal`.
-/

end

end QuasidiagonalMF
end GroupApproximation
