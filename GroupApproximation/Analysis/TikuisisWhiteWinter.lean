import GroupApproximation.Algebra.Amenable
import GroupApproximation.Analysis.CStarExactness
import GroupApproximation.Analysis.MFTracePullback
import GroupApproximation.Analysis.QuasidiagonalTrace
import GroupApproximation.Sofic.ShulmanMFTraceBridge

/-!
# `INT.11` and `CY.12c`: the Tikuisis--White--Winter theorem, stated where it
lives

The manuscript cites Tikuisis--White--Winter twice for the same implication:
in the introduction (`INT.11`, *"all amenable groups are MF, by
quasidiagonality"*) and in the sharpness paragraph (`CY.12c`, the same
sentence at the realized Clifford quotient).  Until now the repository typed
that citation only at its far end, as `QuasidiagonalMF.AmenableMFInput` --- the
bare group implication `amenable ⟹ operator-MF`, with no inhabitant.

**That is not the theorem.**  The theorem is

> Tikuisis, White, Winter, *Quasidiagonality of nuclear C⋆-algebras*,
> Ann. of Math. (2) **185** (2017), 229--284: every faithful trace on a
> separable nuclear C⋆-algebra satisfying the universal coefficient theorem is
> quasidiagonal,

a statement about C⋆-algebras and traces which says nothing about groups; the
group implication is what one gets after four further steps.  Typing the input
at the far end hides which of those steps are theorems.  This file states the
theorem where it lives and walks the four steps, so that exactly one of them
remains a citation.

## The route, and who owns each step

For a countable group `G`, write `τ_r` for the canonical trace of `C⋆_r(G)`
and `q : C⋆(G) → C⋆_r(G)` for the canonical map.

| step | statement | owner |
|---|---|---|
| 1 | `C⋆_r(G)` is separable | `ReducedGroupCStarTrace.reducedGroupCStar_separableSpace` --- **proved** |
| 2 | `τ_r` is a faithful tracial state | `ReducedGroupCStarTrace.canonicalFaithfulTracialState` --- **proved** |
| 3 | `C⋆_r(G)` is nuclear for amenable `G` | `AmenableNuclearInput` --- Lance, **input** |
| 4 | `C⋆_r(G)` satisfies the UCT for amenable `G` | `AmenableUCTInput` --- Tu, **input** |
| 5 | hence `τ_r` is a quasidiagonal trace | `TikuisisWhiteWinterInput` --- TWW, **input** |
| 6 | a quasidiagonal trace is an MF trace | `Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace` --- **proved**, modulo the ucp facts of `Quasidiagonal.UCPContractive` |
| 7 | `τ_r ∘ q` is then an MF trace of `C⋆(G)` | `ShulmanTrace.isMFTrace_canonicalMaximal_of_reducedTrace` --- **proved** |
| 8 | a group whose canonical maximal trace is MF is operator-MF | `ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` --- **proved** |

Steps 6--8 are `isOperatorMF_of_isQuasidiagonalCanonicalTrace` below, and they
are worth reading as one theorem: **the reduction half of `INT.11` is now
proved.**  `Analysis.QuasidiagonalCompression` records that half as
outstanding, with the analytic core done and "matrix-coordinate bookkeeping
against the corona's conventions" left over.  The route taken here avoids that
bookkeeping entirely, by going through the *trace* rather than through a
faithful representation: `Sofic.MFTraceCoronaBridge` already divides bounded
matrix sequences by the null ones and turns an asymptotic homomorphism into an
exact one, and injectivity comes from faithfulness of `τ_r` through the trace
clause rather than from a quasidiagonalizing sequence of projections.

What is left of the printed sentence is steps 3, 4 and 5, and of those only
step 5 is deep.

## What is *not* used

**Hulanicki's theorem is not used.**  The passage from the reduced algebra to
the maximal one is the pullback of trace models along `q`
(`ShulmanTrace.MFTraceModel.comp`), which needs no identification of the two
algebras and no amenability; see `Analysis.MFTracePullback`.

**Nothing here inhabits any input, and nothing here concludes
`QuasidiagonalMF.AmenableMFInput`.**  The conclusions below are stated group by
group, with head `IsOperatorMF`, deliberately: a declaration concluding the
input structure from bare `∀`-premises would enter the discharge fixpoint of
`scripts/check_non_mf_unconditional.py` as a premise-free producer and the
input would stop being reported open.  `Analysis.AmenableMFInput` records the
same decision for the same reason.

## Two nuclearity predicates

The repository carries two, and does not prove them equivalent:
`CStarExactness.IsNuclearCStarAlgebra` (the completely positive approximation
property) and `CStarTensor.IsNuclearCStar` (`min = max` against all test
algebras).  The input below is stated at the **CPAP** form, which is the
definition used in the quasidiagonality literature and the form in which
Lance's theorem produces nuclearity for an amenable group --- the Følner
approximation is an explicit CPAP.  Choi--Effros/Kirchberg relate the two and
neither direction is proved here, so the choice is recorded rather than left
to the reader.
-/

namespace GroupApproximation
namespace QuasidiagonalMF

open ReducedGroupCStarTrace

noncomputable section

universe u

/-! ## The universal coefficient theorem, as a parameter

The UCT is a `KK`-theoretic condition --- `A` is `KK`-equivalent to a
commutative C⋆-algebra --- and `KK`-theory does not exist in this development
or in mathlib, so no honest definition can be given here.  It therefore enters
as a predicate parameter `UCT`, exactly as `NuclearReduced` does in
`Analysis.LanceReduction`.  Every theorem below is universally quantified over
it, so none of them can depend on any property of the UCT beyond its being a
property of the algebra: whatever the reader substitutes, the two places it
occurs --- the hypothesis of `TikuisisWhiteWinterInput` and the conclusion of
`AmenableUCTInput` --- must match, and nothing else about it is available. -/

/-! ## The theorem -/

/-- **The Tikuisis--White--Winter theorem, as a typed input.**

Every faithful trace on a separable nuclear C⋆-algebra satisfying the UCT is
quasidiagonal.  This is the theorem the manuscript's `INT.11` and `CY.12c`
cite, transcribed at the notion in which it is stated
(`Quasidiagonal.IsQuasidiagonalTrace`) rather than at the group implication it
implies.

**No inhabitant is constructed anywhere in this repository, and none can be
without formalizing that theorem.**  It is a structure so that consuming it
leaves a visible binder in the type of every theorem that does.

**Unitality.**  `CStarAlgebra` is mathlib's unital class, so the input is the
unital case of the theorem, and `FaithfulTracialState` is accordingly a
faithful tracial *state*.  That is the case every application here needs ---
`C⋆_r(G)` is unital for every group --- and assuming only the unital case
keeps the input as weak as the use.

The hypotheses on `A` are anonymous explicit binders rather than instance
binders, following `CStarTensor.IsNuclearCStar`: the kernel audit reads an
instance-syntax assumption inside a definition as a finding, and a local
hypothesis of class type is found by instance search just the same. -/
structure TikuisisWhiteWinterInput (UCT : Type u → Prop) : Prop where
  /-- A faithful trace on a separable nuclear UCT C⋆-algebra is
  quasidiagonal. -/
  quasidiagonalTrace : ∀ (A : Type u) (_ : CStarAlgebra A),
    TopologicalSpace.SeparableSpace A →
      CStarExactness.IsNuclearCStarAlgebra A →
        UCT A →
          ∀ τ : FaithfulTracialState A,
            Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)

/-! ## The two group-theoretic inputs the theorem is applied through -/

/-- **Lance's theorem, as a typed input**: the reduced C⋆-algebra of an
amenable group is nuclear.

Lance, *On nuclear C⋆-algebras* (1973).  The repository already carries the
*converse* direction as a hypothesis in `Analysis.LanceReduction` and
`Analysis.NuclearityAmenability`, where it is used to deny nuclearity of the
marked group's algebra; this is the direction the quasidiagonality route
needs, and it is equally unproved here.  Stated at the completely positive
approximation property, which is the form the Følner construction produces.

No inhabitant is constructed here. -/
structure AmenableNuclearInput : Prop where
  /-- The reduced C⋆-algebra of a countable amenable group is nuclear. -/
  nuclear : ∀ (H : Type u) (_ : Group H), Amenability.IsAmenable H →
    CStarExactness.IsNuclearCStarAlgebra (ReducedGroupCStar H)

/-- **The UCT for amenable groups, as a typed input.**

For a discrete amenable group the reduced C⋆-algebra satisfies the universal
coefficient theorem; this is the amenable case of Tu's theorem (Tu, *La
conjecture de Baum--Connes pour les feuilletages moyennables*, 1999), and it
is the second hypothesis of Tikuisis--White--Winter that a group application
has to supply.

It is a separate input from `TikuisisWhiteWinterInput` because it is a
separate theorem with separate authors, and because the abstract `UCT`
parameter would otherwise be pinned by nothing at all.  No inhabitant is
constructed here. -/
structure AmenableUCTInput (UCT : Type u → Prop) : Prop where
  /-- The reduced C⋆-algebra of a countable amenable group satisfies the
  UCT. -/
  uct : ∀ (H : Type u) (_ : Group H), Amenability.IsAmenable H →
    UCT (ReducedGroupCStar H)

/-! ## Step 6--8: the reduction half, proved -/

/-- **The reduction half of `INT.11`: a group whose canonical reduced trace is
quasidiagonal is operator-MF.**

This is the second premise of the factorization
`QuasidiagonalMF.isOperatorMF_of_quasidiagonalRoute`, at the intermediate
predicate the printed words *by quasidiagonality* name --- namely
"the canonical trace of `C⋆_r(G)` is quasidiagonal".  That premise was
outstanding; it is proved here.

Three steps, none of them an input beyond the ucp facts:

* a quasidiagonal trace is an MF trace, forgetting positivity and unitality
  (`Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace`);
* MF traces pull back along the canonical map `C⋆(G) → C⋆_r(G)`, which is how
  the canonical maximal trace is defined
  (`ShulmanTrace.isMFTrace_canonicalMaximal_of_reducedTrace`);
* a group whose canonical maximal trace is an MF trace is operator-MF, by the
  corona argument of `Sofic.MFTraceCoronaBridge`
  (`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal`).

No countability, amenability or nuclearity hypothesis appears: those belong to
the *other* half. -/
theorem isOperatorMF_of_isQuasidiagonalCanonicalTrace
    (hucp : Quasidiagonal.UCPContractive.{u})
    (G : Type u) [Group G]
    (h : Quasidiagonal.IsQuasidiagonalTrace
      (fun T : ReducedGroupCStar G ↦
        ReducedGroupCStarTrace.canonicalFaithfulTracialState G T)) :
    IsOperatorMF G :=
  ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal
    (ShulmanTrace.isMFTrace_canonicalMaximal_of_reducedTrace G
      (Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace hucp h))

/-! ## Steps 1--5: the theorem half, at the reduced algebra of an amenable
group -/

/-- **The first premise of the printed factorization.**  Granting
Tikuisis--White--Winter, Lance and Tu, the canonical trace of the reduced
C⋆-algebra of a countable amenable group is quasidiagonal.

The two clauses the manuscript's own development supplies are visible in the
proof: separability is `reducedGroupCStar_separableSpace`, faithfulness is
`canonicalFaithfulTracialState`.  Both are theorems here, so a reader can see
that the four hypotheses of Tikuisis--White--Winter are met by two theorems
and two further citations, not by four citations. -/
theorem isQuasidiagonalTrace_canonicalReduced_of_amenable
    {UCT : Type u → Prop} (tww : TikuisisWhiteWinterInput UCT)
    (lance : AmenableNuclearInput.{u}) (tu : AmenableUCTInput.{u} UCT)
    (G : Type u) [Group G] [Countable G]
    (hA : Amenability.IsAmenable G) :
    Quasidiagonal.IsQuasidiagonalTrace
      (fun T : ReducedGroupCStar G ↦
        ReducedGroupCStarTrace.canonicalFaithfulTracialState G T) :=
  tww.quasidiagonalTrace (ReducedGroupCStar G) inferInstance
    (ReducedGroupCStarTrace.reducedGroupCStar_separableSpace G)
    (lance.nuclear G inferInstance hA) (tu.uct G inferInstance hA)
    (ReducedGroupCStarTrace.canonicalFaithfulTracialState G)

/-! ## The printed sentence -/

/-- **`INT.11`, group by group, over the inputs it actually rests on.**

Every countable amenable group is operator-MF, granting: the ucp facts, the
Tikuisis--White--Winter theorem, Lance's nuclearity theorem, and the UCT for
amenable groups.  Nothing else --- in particular no property of the abstract
`UCT` parameter, no identification of `C⋆(G)` with `C⋆_r(G)`, and no
approximation argument beyond the corona quotient.

**The conclusion is `IsOperatorMF G` and not
`QuasidiagonalMF.AmenableMFInput`, deliberately**; see the module docstring.
A reader who wants the input recovers it by universally quantifying this
statement, which asserts nothing further. -/
theorem isOperatorMF_of_isAmenable_of_tww {UCT : Type u → Prop}
    (hucp : Quasidiagonal.UCPContractive.{u})
    (tww : TikuisisWhiteWinterInput UCT)
    (lance : AmenableNuclearInput.{u}) (tu : AmenableUCTInput.{u} UCT)
    (G : Type u) [Group G] [Countable G]
    (hA : Amenability.IsAmenable G) :
    IsOperatorMF G :=
  isOperatorMF_of_isQuasidiagonalCanonicalTrace hucp G
    (isQuasidiagonalTrace_canonicalReduced_of_amenable tww lance tu G hA)

/-- **The contrapositive**, which is the shape `sec:consequences` uses: a
countable group that is not operator-MF is not amenable. -/
theorem not_isAmenable_of_not_isOperatorMF_of_tww {UCT : Type u → Prop}
    (hucp : Quasidiagonal.UCPContractive.{u})
    (tww : TikuisisWhiteWinterInput UCT)
    (lance : AmenableNuclearInput.{u}) (tu : AmenableUCTInput.{u} UCT)
    (G : Type u) [Group G] [Countable G]
    (hMF : ¬ IsOperatorMF G) :
    ¬ Amenability.IsAmenable G :=
  fun hA ↦ hMF (isOperatorMF_of_isAmenable_of_tww hucp tww lance tu G hA)

end

end QuasidiagonalMF
end GroupApproximation
