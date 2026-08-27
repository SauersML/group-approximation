import GroupApproximation.Manuscript.NinetyNineProblems.FactorizationProperty
import GroupApproximation.Manuscript.NinetyNineProblems.ProblemXGroups
import GroupApproximation.Manuscript.OneSidedMFRadical.HeadlineTheorem
import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Meta.AxiomGuard

/-!
# Property `(T)` makes amenable traces quasidiagonal

Problem X(1) of Schafhauser--Tikuisis--White asks whether every amenable trace
is quasidiagonal.  On full group C⋆-algebras of **Kazhdan** groups the answer
is yes, and has been since 1994.  This file states that positive instance,
takes it as a typed input, and spends it on the manuscript's own group.

## The mechanism

Kirchberg, *Discrete groups with Kazhdan's property T and factorization
property are residually finite*, Math. Ann. **299** (1994), 551--563,
Proposition 2.3 --- printed as Brown, Mem. Amer. Math. Soc. **184** (2006),
no. 865, Lemma 4.1.11 --- is a **rigidity** statement: for a Kazhdan group `Γ`,
u.c.p. maps on `C⋆(Γ)` that are asymptotically multiplicative in the
*Hilbert--Schmidt* norm are uniformly close to honest finite-dimensional
**representations**, with the same limiting characters.  Property `(T)` is
what pays for the upgrade: an almost-invariant vector for the associated
representation must be near an invariant one, and the Kazhdan projection turns
that into a norm estimate the `2`-norm alone cannot give.

Brown's Proposition 4.1.12 is the consequence: on `C⋆(Γ)` with `Γ` Kazhdan,
every amenable trace is quasidiagonal --- indeed locally finite-dimensional,
since the approximating maps are genuine representations.

`KirchbergKazhdanQuasidiagonalInput` below is that consequence, at the
canonical trace.  It is assumed, not proved: the repository has neither
Kazhdan projections in `C⋆(Γ) ⊗ C⋆(Γ)` nor the perturbation theory the upgrade
runs on.

## What it buys, and against which group

Two things, and they point in opposite directions.

**A positive instance of Problem X(1).**
`problemX1_restricted_to_kazhdan` records that X(1) *holds* on Kazhdan full
group C⋆-algebras.  Any counterexample to X(1) among group algebras must
therefore come from a non-Kazhdan group --- which is a real constraint on the
search, and one the manuscript's own headline group fails.

**A second, independent proof that `H` lacks the factorization property.**
`Manuscript/NinetyNineProblems/FactorizationProperty.lean` already derives
`¬ HasFactorizationProperty H` from Kirchberg's *other* 1994 theorem, through
residual finiteness: `H` is infinite and simple, so not residually finite, so
by `(T)` + factorization ⟹ residually finite it has no factorization property.

`rankTwelveLeavitt_not_hasFactorizationProperty'` below reaches the same
conclusion **without using simplicity or residual finiteness at all**.  It uses
only that `H` is Kazhdan and not MF: were `H` to have the factorization
property, its canonical trace would be amenable, hence quasidiagonal by
Brown 4.1.12, hence an MF trace, hence `H` operator-MF --- contradicting
Theorem B.  Two routes, disjoint hypotheses, same conclusion; the agreement is
a check on both.

## What it does not buy, and why `E` is untouched

Nothing here says anything about the literal group `E` of
`Manuscript/NinetyNineProblems/ProblemX.lean`, because the mechanism needs
property `(T)` **for the whole group** and `E` is not a Kazhdan group in this
development: no declaration asserts `HasKazhdanPropertyT MarkedGroup`, and
property `(T)` enters the telescope construction only as a hypothesis on a base
group (`Sofic/AscendingHNNFullTelescopeRadical.lean` carries it as
`hΓ : HasKazhdanPropertyT.{0,0} Γ₀`).

So for `E` the same rigidity would have to run **relative to the Kazhdan base
sitting inside `E`**, transporting the `(T)` estimate from the base to the
whole telescope through the u.c.p. Hilbert--Schmidt models.  That relative
transport is exactly the open question, and it is the same open leaf as
`LiteralFactorizationProperty`: `ProblemX.lean` leaves the trace's amenability
open, and this file explains what a proof of it would have to survive.  The
`(T)`-rigidity half is what is stated here; the relative half is not stated
anywhere, because no one has it.
-/

namespace GroupApproximation
namespace NinetyNineProblems

open Manuscript.OneSidedMFRadical

universe u

/-! ## Kirchberg's rigidity, as a typed input -/

/-- **Brown's Proposition 4.1.12, as a typed input.**

> Brown, Mem. Amer. Math. Soc. **184** (2006), no. 865, Proposition 4.1.12,
> from his Lemma 4.1.11 = Kirchberg, Math. Ann. **299** (1994), Proposition
> 2.3: for a countable group `Γ` with property `(T)`, every amenable trace on
> `C⋆(Γ)` is quasidiagonal.

Stated at the canonical trace, which is where this development consumes it,
and with `[Countable G]` kept because that is Brown's setting.

No inhabitant is constructed.  The proof upgrades Hilbert--Schmidt
asymptotically multiplicative u.c.p. maps to finite-dimensional
representations using the Kazhdan projection, and neither that projection nor
the perturbation argument exists in this repository.

The Kazhdan hypothesis is read at representation-space universe `u`, matching
`KirchbergKazhdanFactorizationInput` in
`Manuscript/NinetyNineProblems/FactorizationProperty.lean` and the
`HasKazhdanPropertyT.{0, 0}` the concrete groups are stated with. -/
structure KirchbergKazhdanQuasidiagonalInput : Prop where
  /-- On a countable Kazhdan group, the canonical trace of the full group
  C⋆-algebra is quasidiagonal as soon as it is amenable. -/
  quasidiagonal : ∀ (G : Type u) [Group G] [Countable G],
    HasKazhdanPropertyT.{u, u} G →
      Quasidiagonal.IsAmenableTrace
          (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) →
        Quasidiagonal.IsQuasidiagonalTrace
          (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a)

/-- **Problem X(1) holds on Kazhdan full group C⋆-algebras.**

The input restated in the vocabulary of the factorization property, which by
Brown's Theorem 4.1.9 is what amenability of the canonical trace means.  Worth
a name of its own: it is a *positive* instance of Problem X(1), and it says
that any group-algebra counterexample to X(1) must come from a non-Kazhdan
group. -/
theorem problemX1_restricted_to_kazhdan
    (k : KirchbergKazhdanQuasidiagonalInput.{u}) (G : Type u) [Group G]
    [Countable G] (hT : HasKazhdanPropertyT.{u, u} G)
    (hFP : HasFactorizationProperty G) :
    Quasidiagonal.IsQuasidiagonalTrace
      (fun a : MaximalGroupCStar G ↦ canonicalMaximalTrace G a) :=
  k.quasidiagonal G hT hFP

/-! ## The consequence for MF-ness -/

/-- **A Kazhdan group with the factorization property is operator-MF.**

Three steps, the last two already in the repository.  The input makes the
canonical trace quasidiagonal; `Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace`
makes it an MF trace, the tracial-state datum being
`ShulmanTrace.canonicalMaximalTracialState` and the contractivity of u.c.p.
maps being `Quasidiagonal.ucpContractive`; and
`ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` carries that to the
group through the norm-matrix corona.

This is the maximal-trace route of
`Manuscript/NinetyNineProblems/ProblemXGroups.lean`, run from the Kazhdan
input rather than from Problem X(1) itself. -/
theorem isOperatorMF_of_kazhdan_hasFactorizationProperty
    (k : KirchbergKazhdanQuasidiagonalInput.{u}) (G : Type u) [Group G]
    [Countable G] (hT : HasKazhdanPropertyT.{u, u} G)
    (hFP : HasFactorizationProperty G) : IsOperatorMF G :=
  ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal
    (Quasidiagonal.isMFTrace_of_isQuasidiagonalTrace
      (IsTracialState.of_bundled (ShulmanTrace.canonicalMaximalTracialState G))
      Quasidiagonal.ucpContractive
      (problemX1_restricted_to_kazhdan k G hT hFP))

/-- **A Kazhdan group that is not MF has no factorization property.**  The
contrapositive, and the form the manuscript's group is fed into. -/
theorem not_hasFactorizationProperty_of_kazhdan_not_operatorMF
    (k : KirchbergKazhdanQuasidiagonalInput.{u}) (G : Type u) [Group G]
    [Countable G] (hT : HasKazhdanPropertyT.{u, u} G)
    (hnot : ¬ IsOperatorMF G) : ¬ HasFactorizationProperty G := fun hFP ↦
  hnot (isOperatorMF_of_kazhdan_hasFactorizationProperty k G hT hFP)

/-! ## The manuscript's group, by a second route -/

/-- **The rank-twelve binary Leavitt elementary group is not operator-MF.**

Theorem B, read through the equivalence of the literal CDE corona definition
with the unitary-sequence one.  `manuscriptBinaryLeavittHeadline` is
unconditional, and its last component is `¬ IsCDEOperatorMF H`. -/
theorem rankTwelveLeavitt_not_isOperatorMF :
    ¬ IsOperatorMF RankTwelveEndpoint.H := by
  haveI : Countable RankTwelveEndpoint.H := RankTwelveEndpoint.countable
  intro hMF
  exact manuscriptBinaryLeavittHeadline.2.2.2.2.2
    ((isCDEOperatorMF_iff_isOperatorMF RankTwelveEndpoint.H).mpr hMF)

/-- **`H` has no factorization property --- second proof.**

Independent of the first.  `FactorizationProperty.lean` argues through
residual finiteness and needs `H` to be infinite and simple;
this argument uses **neither**.  It needs only that `H` is Kazhdan
(`RankTwelveEndpoint.hasKazhdanPropertyT`) and not MF
(`rankTwelveLeavitt_not_isOperatorMF`, i.e. Theorem B), against Brown's
Proposition 4.1.12.

The two proofs consume different citations as well --- Kirchberg's residual
finiteness theorem there, Kirchberg's u.c.p. rigidity here --- so the
agreement is a genuine cross-check on the placement of `H`, not a
restatement.

As with the first proof, this says nothing about `E`; see the module
docstring. -/
theorem rankTwelveLeavitt_not_hasFactorizationProperty'
    (k : KirchbergKazhdanQuasidiagonalInput.{0}) :
    ¬ HasFactorizationProperty RankTwelveEndpoint.H := by
  haveI : Countable RankTwelveEndpoint.H := RankTwelveEndpoint.countable
  exact not_hasFactorizationProperty_of_kazhdan_not_operatorMF k
    RankTwelveEndpoint.H RankTwelveEndpoint.hasKazhdanPropertyT
    rankTwelveLeavitt_not_isOperatorMF

end NinetyNineProblems
end GroupApproximation

open GroupApproximation.NinetyNineProblems

#audit_axioms KirchbergKazhdanQuasidiagonalInput
#audit_axioms problemX1_restricted_to_kazhdan
#audit_axioms isOperatorMF_of_kazhdan_hasFactorizationProperty
#audit_axioms not_hasFactorizationProperty_of_kazhdan_not_operatorMF
#audit_closed_axioms rankTwelveLeavitt_not_isOperatorMF
#audit_axioms rankTwelveLeavitt_not_hasFactorizationProperty'
