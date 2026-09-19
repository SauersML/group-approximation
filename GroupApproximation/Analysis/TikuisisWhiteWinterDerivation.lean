import GroupApproximation.Analysis.TikuisisWhiteWinterProof
import GroupApproximation.Analysis.TikuisisWhiteWinterCore
import GroupApproximation.Analysis.QuasidiagonalCoronaCriterion

/-!
# Tikuisis--White--Winter, derived rather than assumed

`Analysis.TikuisisWhiteWinterProof` states `TikuisisWhiteWinterTheorem` --- the
Annals theorem at the defined UCT --- as a structure, and assumes it.  This
file removes that assumption: **`TikuisisWhiteWinterTheorem` is produced here,
in two independent ways, each from strictly finer named inputs.**

That is not a proof of the theorem, and this file does not claim one.  It is
the difference between assuming a named theorem and assuming the ingredients
its published proof consumes, with every step between them proved.  The
statement `TikuisisWhiteWinterTheorem T` no longer needs to appear as a
hypothesis anywhere in this development.

## Derivation 1: from the corona form

What the Annals argument produces at the end of its run through the
Kirchberg--Rørdam corona theory is a unital `⋆`-homomorphism `A → ℓ∞/c₀` that
lifts to unital completely positive matrix maps and carries the trace.  That
is `Quasidiagonal.HasCoronaModel`, and
`Quasidiagonal.isQuasidiagonalTrace_of_hasCoronaModel` --- **proved**, in
`Analysis.QuasidiagonalCoronaCriterion` --- turns it into quasidiagonality of
the trace.  So the input can be stated in the form the theorem is *proved* in,
and the translation into the form it is *stated* in is a theorem here.

`CoronaEmbeddingInput` is that input, and
`tikuisisWhiteWinterTheorem_of_coronaEmbedding` is the derivation.

## Derivation 2: from Connes--Haagerup and the local core

`Analysis.TikuisisWhiteWinterCore` already splits the citation along its other
natural seam: the Annals theorem proper hypothesizes an *amenable* trace and
concludes *local* quasidiagonality, and two further steps --- that every trace
on a nuclear algebra is amenable (Connes, Haagerup, Choi--Effros) and that
local quasidiagonality upgrades to the sequence form (proved there) --- close
the gap.

`tikuisisWhiteWinterTheorem_of_core` re-runs that assembly at the defined UCT.
The only new ingredient it needs is a *link*: the abstract predicate the core
input is stated over must be implied by `SatisfiesUCT`.  `uctExists` is such a
predicate and the link is proved for it, so the derivation is unconditional in
the UCT.

## Two predicates, and why both

A `Type u → Prop` cannot see a C⋆-structure, so translating `SatisfiesUCT`
into that shape requires a choice of quantifier, and the two directions need
opposite choices:

* `uctPredicate` (universal, in `Analysis.TikuisisWhiteWinterProof`) is what
  one must **produce** to feed the old `TikuisisWhiteWinterInput`, so the
  universal form --- harder to satisfy --- is the one that makes the old input
  easier to construct;
* `uctExists` (existential, here) is what one must **consume** from a core
  input, so the existential form --- easier to satisfy --- is the one for
  which the link from `SatisfiesUCT` is provable.

Neither is a weakening in disguise: each is used in exactly one direction, and
the direction is recorded at the definition.

## What is still assumed, after this file

Four published theorems, none of which is Tikuisis--White--Winter's statement:

* `KK.KasparovTheory` (Kasparov);
* whichever of `CoronaEmbeddingInput` (the corona form of the Annals argument)
  or `NuclearAmenableTraceInput` + `TikuisisWhiteWinterCoreInput` (Connes--
  Haagerup plus the Annals argument in its local, amenable-trace form) the
  reader prefers;
* `KK.DadarlatEilersInput`, `OrderZero.WinterZachariasInput` and
  `OrderZero.CoronaOrderZeroLiftInput`, which are what a proof of the
  remaining input would consume, and which nothing here consumes.

The honest summary has not changed --- the Annals theorem is not proved here
and cannot be --- but the surface on which it is assumed is now stated in the
vocabulary of its own proof, and every step from that vocabulary to the
manuscript's sentence is machine-checkable.
-/

namespace GroupApproximation
namespace QuasidiagonalMF

open ReducedGroupCStarTrace
open KK

noncomputable section

universe u

/-! ## The existential UCT predicate, and the link -/

/-- **The UCT as a predicate on types, existential form.**  A type satisfies it
when *some* separable C⋆-structure on it lies in the bootstrap class.

This is the form that can be *produced* from `SatisfiesUCT`, and it is what a
`TikuisisWhiteWinterCoreInput` should be taken over when the goal is to derive
the theorem at the defined UCT.  Contrast `uctPredicate`, the universal form,
which is what must be produced to feed the old
`TikuisisWhiteWinterInput`. -/
def uctExists (T : KasparovTheory.{u}) (A : Type u) : Prop :=
  ∃ S : SepCStarAlgebra.{u}, S.carrier = A ∧ T.SatisfiesUCT S

/-- **The link**: a bootstrap-class algebra has a bootstrap-class underlying
type.  Proved, and it is the only thing `tikuisisWhiteWinterTheorem_of_core`
needs beyond the two published inputs. -/
theorem uctExists_of_satisfiesUCT {T : KasparovTheory.{u}}
    (S : SepCStarAlgebra.{u}) (h : T.SatisfiesUCT S) :
    uctExists T S.carrier :=
  ⟨S, rfl, h⟩

/-! ## Derivation 1: the corona form -/

/-- **The Annals theorem in the form it is proved in, as a typed input.**

A faithful trace on a nuclear bootstrap-class algebra admits a *corona model*:
unital completely positive matrix models whose induced map into `ℓ∞/c₀` is
multiplicative on the nose and whose normalized traces converge to the trace.

This is weaker than `TikuisisWhiteWinterTheorem` in the only sense that
matters here --- it is the same mathematics one step earlier, before the
translation back into asymptotic language, and that translation is proved
(`Quasidiagonal.isQuasidiagonalTrace_of_hasCoronaModel`).

No inhabitant is constructed here. -/
structure CoronaEmbeddingInput (T : KasparovTheory.{u}) : Prop where
  /-- A faithful trace on a nuclear bootstrap-class algebra has a corona
  model. -/
  hasCoronaModel : ∀ S : SepCStarAlgebra.{u},
    CStarExactness.IsNuclearCStarAlgebra S →
      T.SatisfiesUCT S →
        ∀ τ : FaithfulTracialState S,
          Quasidiagonal.HasCoronaModel (fun a : S => τ a)

/-- **Derivation 1**: the corona form of the Annals argument gives the theorem.

The content of the step is `Analysis.QuasidiagonalCoronaCriterion`: an exact
product identity in the corona is an asymptotic product identity in the matrix
algebras, which is the multiplicativity clause of
`QuasidiagonalTraceModel`. -/
theorem tikuisisWhiteWinterTheorem_of_coronaEmbedding {T : KasparovTheory.{u}}
    (emb : CoronaEmbeddingInput T) : TikuisisWhiteWinterTheorem T where
  quasidiagonal S hnuc huct τ :=
    Quasidiagonal.isQuasidiagonalTrace_of_hasCoronaModel
      (emb.hasCoronaModel S hnuc huct τ)

/-! ## Derivation 2: Connes--Haagerup and the local core -/

/-- **Derivation 2**: the Annals theorem in its own local, amenable-trace form,
together with Connes--Haagerup, gives the theorem at the defined UCT.

The step that is not a citation is the diagonal argument
`Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`, already
proved in `Analysis.QuasidiagonalTraceLocal` and consumed through
`isQuasidiagonalTrace_of_core`.  Separability comes from the bundled object,
so it is not a hypothesis here at all. -/
theorem tikuisisWhiteWinterTheorem_of_core {T : KasparovTheory.{u}}
    {UCT : Type u → Prop} (connes : NuclearAmenableTraceInput.{u})
    (core : TikuisisWhiteWinterCoreInput.{u} UCT)
    (hlink : ∀ S : SepCStarAlgebra.{u}, T.SatisfiesUCT S → UCT S.carrier) :
    TikuisisWhiteWinterTheorem T where
  quasidiagonal S hnuc huct τ :=
    isQuasidiagonalTrace_of_core connes core S S.separable hnuc
      (hlink S huct) τ

/-- **Derivation 2, with the link discharged.**  Taking the core input over
`uctExists` removes the abstract predicate entirely: the only hypotheses are
the two published theorems. -/
theorem tikuisisWhiteWinterTheorem_of_core_uctExists {T : KasparovTheory.{u}}
    (connes : NuclearAmenableTraceInput.{u})
    (core : TikuisisWhiteWinterCoreInput.{u} (uctExists T)) :
    TikuisisWhiteWinterTheorem T :=
  tikuisisWhiteWinterTheorem_of_core connes core
    fun S h => uctExists_of_satisfiesUCT S h

/-! ## The group endpoints, with no `TikuisisWhiteWinterTheorem` binder -/

/-- **`INT.11` over the corona form.**  Every countable amenable group is
operator-MF, granting the corona form of the Annals argument, Lance and Tu.

The ucp binder is discharged by `Quasidiagonal.ucpContractive`, a theorem of
this development, so it does not appear. -/
theorem isOperatorMF_of_isAmenable_of_coronaEmbedding {T : KasparovTheory.{u}}
    (emb : CoronaEmbeddingInput T) (lance : AmenableNuclearInput.{u})
    (tu : ∀ (H : Type u) (_ : Group H) (_ : Countable H),
      Amenability.IsAmenable H → T.SatisfiesUCT (reducedObject H))
    (G : Type u) [Group G] [Countable G] (hA : Amenability.IsAmenable G) :
    IsOperatorMF G :=
  isOperatorMF_of_isAmenable Quasidiagonal.ucpContractive
    (tikuisisWhiteWinterTheorem_of_coronaEmbedding emb) lance tu G hA

/-- **`INT.11` over Connes--Haagerup and the local core**, at the defined
UCT. -/
theorem isOperatorMF_of_isAmenable_of_coreUCT {T : KasparovTheory.{u}}
    (connes : NuclearAmenableTraceInput.{u})
    (core : TikuisisWhiteWinterCoreInput.{u} (uctExists T))
    (lance : AmenableNuclearInput.{u})
    (tu : ∀ (H : Type u) (_ : Group H) (_ : Countable H),
      Amenability.IsAmenable H → T.SatisfiesUCT (reducedObject H))
    (G : Type u) [Group G] [Countable G] (hA : Amenability.IsAmenable G) :
    IsOperatorMF G :=
  isOperatorMF_of_isAmenable Quasidiagonal.ucpContractive
    (tikuisisWhiteWinterTheorem_of_core_uctExists connes core) lance tu G hA

/-- **The old parameterized input, from the corona form.**  Everything
`Analysis.TikuisisWhiteWinter` proves is therefore available from the corona
form of the Annals argument, with no `TikuisisWhiteWinterInput` and no
`TikuisisWhiteWinterTheorem` assumed anywhere. -/
theorem tikuisisWhiteWinterInput_of_coronaEmbedding {T : KasparovTheory.{u}}
    (emb : CoronaEmbeddingInput T) :
    TikuisisWhiteWinterInput (uctPredicate T) :=
  tikuisisWhiteWinterInput_of_theorem
    (tikuisisWhiteWinterTheorem_of_coronaEmbedding emb)

end

end QuasidiagonalMF
end GroupApproximation
