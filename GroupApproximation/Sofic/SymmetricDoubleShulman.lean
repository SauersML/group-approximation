import GroupApproximation.Sofic.TerminalQuotientIso
import GroupApproximation.Sofic.SigmaGroupMF
import GroupApproximation.Sofic.SymmetricDoubleMF

/-!
# The last input, in every form it can be supplied, and its exact strength

`Sofic/TerminalQuotientIso` proves the manuscript's presentation calculation as
a theorem (`terminalEquiv`), leaving

```text
IsOperatorMF (SymmetricDouble SigmaGroup sigmaBase)
```

as the single remaining input of the exact MF-radical computation
(`manuscriptExactRadical_of_symmetricDoubleMF`).  This file does three things to
that input, and does not prove it.

## 1. The input is *equivalent* to the endpoint, not merely sufficient for it

`manuscriptExactRadical_iff_symmetricDoubleMF` proves both directions.  The
forward one is the existing wrapper.  The reverse one is new: from the two
radical identities the symmetric double is recovered as operator MF, through
`AmalgamMFTrace.exactRadical_iff_isOperatorMF_symmetricDouble` fed with
`terminalEquiv` transported along the defect equality
(`QuotientGroup.quotientMulEquivOfEq`).

The consequence is a statement about the *program*, not about the group: no
weakening of the analytic input can reach the endpoint, because the endpoint
already implies the input.  Anything advertised as a cheaper route to the exact
radical is therefore either false, or a disguised proof of the
symmetric-amalgamation theorem.

## 2. Every entry point is composed to the endpoint

The input can be supplied at four different altitudes, and each is wired here
straight to the manuscript's three-conjunct conclusion:

* an **MF trace** on `C⋆(Σ *_B Σ)` in Shulman's sense
  (`manuscriptExactRadical_of_isMFTrace_symmetricDouble`) --- the altitude the
  C⋆-theorem is proved at;
* a **finite-test-set matrix model** for the regular character of the double
  (`manuscriptExactRadical_of_isMFRegularCharacter_symmetricDouble`) --- the
  altitude with no C⋆-algebra in it at all: finitely many complex matrices, an
  operator-norm multiplicativity defect, and two normalized-trace estimates;
* operator MF of the **free-lamp amalgam** `Σ *_B (B × C₂)`
  (`manuscriptExactRadical_of_terminalAmalgam_isOperatorMF`), through the
  unconditional covering equivalence;
* the **general symmetric-amalgamation sentence**, quantified over all pairs,
  in either the MF-factor or the residually-finite-factor form
  (`manuscriptExactRadical_of_shulmanSymmetricAmalgamation`,
  `manuscriptExactRadical_of_shulmanResiduallyFiniteDouble`).  Both side
  conditions on the factor are discharged here rather than assumed:
  `Countable SigmaGroup` is an instance and `sigmaGroup_isOperatorMF`,
  `sigmaGroup_residuallyFinite` are theorems of `Sofic/SigmaGroupMF`.

The second altitude is the useful one for a formalization attempt.  It is
`MFTraceRecognition.IsMFRegularCharacter`, and it mentions no C⋆-algebra, no
trace on an algebra, and no completion: it asks, for each finite `F ⊆ Σ *_B Σ`
and each `ε > 0`, for one finite matrix model of `F` accurate to `ε`.

## 3. The pair is not one of the pairs the input is false for

`KunThomShulmanDouble.exists_not_isOperatorMF_symmetricDouble` refutes the
symmetric-amalgamation sentence for *arbitrary* pairs, so it is worth recording
precisely why that refutation does not reach here.  It is run at `Γ = ⊤`, where
the double collapses to the factor and the factor is the manuscript's non-MF
group.  For `(Σ, B)` both halves of that fail:

* `sigmaBase_ne_top` --- `B ≠ ⊤`, because the half-translation `s = t⁻¹ v₁ t`
  is not in `B` (`SymmetricDoubleMF.escapeElement_not_mem_sigmaBase`);
* `sigmaGroup_isOperatorMF` --- the factor *is* operator MF.

`sigmaBase_not_normal` adds the one-line reason the amalgam is not a direct
product in disguise: the same escape element is a conjugate of `v₁ ∈ B` that
leaves `B`, so the Bass--Serre witness the whole construction rests on is not
formally trivial.

`symmetricDoubleShulman_state` collects the five facts in one proposition.

## What is not here

No matrix models for the double are constructed, and no clause of
`ShulmanTrace.MFTraceModel` is verified for it.  That is the entire remaining
content, and it is genuinely the C⋆-theorem: `Sofic/SymmetricDoubleMF` proves
the exact-model routes are closed (`B` is not separable in `Σ`), so the models
must be approximate, and an approximate model for an amalgam is produced by
freeness with amalgamation over `C⋆(B)`, which this repository does not have.
-/

namespace GroupApproximation
namespace TerminalQuotientPresentation

open LiteralNonMFPresentation LiteralSignFreeQuotient
open LiteralSignFreeRadicalReduction

noncomputable section

/-! ## The pair `(Σ, B)` is not a refuted pair

`Sofic/DoubleInputsMinimal` refutes the symmetric-amalgamation sentence over
arbitrary pairs by taking `Γ = ⊤`.  Neither of the two features that
counterexample relies on is present here. -/

/-- **`B` is a proper subgroup of `Σ`.**  The half-translation
`s = t⁻¹ v₁ t` escapes it, by
`SymmetricDoubleMF.escapeElement_not_mem_sigmaBase`.

This is what separates the pair from the `Γ = ⊤` counterexample of
`KunThomShulmanDouble.exists_not_isOperatorMF_symmetricDouble`, where the double
collapses onto the factor and inherits its failure. -/
theorem sigmaBase_ne_top : sigmaBase ≠ ⊤ := by
  intro h
  refine SymmetricDoubleMF.escapeElement_not_mem_sigmaBase ?_
  rw [h]
  exact Subgroup.mem_top _

/-- **`B` is not normal in `Σ`.**  The marked translation `v₁` lies in `B` and
its conjugate `t⁻¹ v₁ t` does not, which is the same escape element again.

Non-normality is what makes the amalgam larger than the factor: it is the
hypothesis `Sofic/InfranormalCompressionPair.exists_escape_of_not_normal`
consumes, and by `nonempty_escapeWitness_iff` it is
*exactly* the four combinatorial fields of the double datum. -/
theorem sigmaBase_not_normal : ¬ sigmaBase.Normal := by
  intro h
  refine SymmetricDoubleMF.escapeElement_not_mem_sigmaBase ?_
  rw [SymmetricDoubleMF.escapeElement_eq]
  have hc := h.conj_mem SymmetricDoubleMF.sigmaUnit
    SymmetricDoubleMF.sigmaUnit_mem_sigmaBase SymmetricDoubleMF.sigmaStable⁻¹
  rwa [inv_inv] at hc

/-! ## The four altitudes at which the input can be supplied -/

/-- **Trace altitude.**  An MF trace on the full group C⋆-algebra of the
symmetric double, in Shulman's five-clause sense, gives operator MF of the
double.  This is `ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal` at
the literal pair; nothing is left to discharge on the way. -/
theorem isOperatorMF_symmetricDouble_of_isMFTrace
    (h : ShulmanTrace.IsMFTrace
      (fun a : MaximalGroupCStar (SymmetricDouble SigmaGroup sigmaBase) ↦
        canonicalMaximalTrace (SymmetricDouble SigmaGroup sigmaBase) a)) :
    IsOperatorMF (SymmetricDouble SigmaGroup sigmaBase) :=
  ShulmanTrace.isOperatorMF_of_isMFTrace_canonicalMaximal h

/-- **Finite-matrix altitude.**  The finite-test-set condition
`MFTraceRecognition.IsMFRegularCharacter` for the symmetric double already
gives operator MF of it.

This is the weakest shape the last input takes anywhere in the library, and it
is the one to aim a construction at: unfolded, it asks for a bound
`B : Σ *_B Σ → ℝ` chosen once, and then, for every finite `F` and every
`ε > 0`, a single nonempty finite index type with matrices `φ(g)` bounded by
`B g`, multiplicative on `F` to accuracy `ε` in the operator norm,
adjoint-compatible on `F` to the same accuracy, and correct in normalized
trace at `1` and away from `1` to that accuracy.  No C⋆-algebra, no
completion and no trace on an algebra occur in that statement. -/
theorem isOperatorMF_symmetricDouble_of_isMFRegularCharacter
    (h : MFTraceRecognition.IsMFRegularCharacter
      (SymmetricDouble SigmaGroup sigmaBase)) :
    IsOperatorMF (SymmetricDouble SigmaGroup sigmaBase) :=
  OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr
    (MFTraceRecognition.isNormApproximable_of_isMFRegularCharacter
      (SymmetricDouble SigmaGroup sigmaBase) h)

/-- **Free-lamp altitude.**  Operator MF of the terminal amalgam
`Σ *_B (B × C₂)` gives operator MF of the symmetric double, by the
unconditional covering equivalence of `Sofic/SymmetricDoubleCovering`. -/
theorem isOperatorMF_symmetricDouble_of_terminalAmalgam
    (h : IsOperatorMF TerminalAmalgam) :
    IsOperatorMF (SymmetricDouble SigmaGroup sigmaBase) :=
  (isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble
    SigmaGroup sigmaBase).mp h

/-! ## The endpoint from each altitude -/

/-- The manuscript's exact residual computation from an MF trace on the
symmetric double, with the presentation calculation already discharged by
`terminalEquiv`. -/
theorem manuscriptExactRadical_of_isMFTrace_symmetricDouble
    (h : ShulmanTrace.IsMFTrace
      (fun a : MaximalGroupCStar (SymmetricDouble SigmaGroup sigmaBase) ↦
        canonicalMaximalTrace (SymmetricDouble SigmaGroup sigmaBase) a)) :
    signFreeCollapseDefect = signFreePrintedDefect ∧
      actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect ∧
        actualCoronaMFResidual MarkedGroup =
          signFreeCollapseDefect.comap proj :=
  manuscriptExactRadical_of_symmetricDoubleMF
    (isOperatorMF_symmetricDouble_of_isMFTrace h)

/-- The manuscript's exact residual computation from finite matrix models for
the regular character of the symmetric double.  This is the whole endpoint
resting on a statement with no C⋆-algebra in it. -/
theorem manuscriptExactRadical_of_isMFRegularCharacter_symmetricDouble
    (h : MFTraceRecognition.IsMFRegularCharacter
      (SymmetricDouble SigmaGroup sigmaBase)) :
    signFreeCollapseDefect = signFreePrintedDefect ∧
      actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect ∧
        actualCoronaMFResidual MarkedGroup =
          signFreeCollapseDefect.comap proj :=
  manuscriptExactRadical_of_symmetricDoubleMF
    (isOperatorMF_symmetricDouble_of_isMFRegularCharacter h)

/-- The manuscript's exact residual computation from operator MF of the
free-lamp amalgam `Σ *_B (B × C₂)`. -/
theorem manuscriptExactRadical_of_terminalAmalgam_isOperatorMF
    (h : IsOperatorMF TerminalAmalgam) :
    signFreeCollapseDefect = signFreePrintedDefect ∧
      actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect ∧
        actualCoronaMFResidual MarkedGroup =
          signFreeCollapseDefect.comap proj :=
  manuscriptExactRadical_of_symmetricDoubleMF
    (isOperatorMF_symmetricDouble_of_terminalAmalgam h)

/-! ## The general sentence, with both side conditions on the factor discharged

Shulman's Theorem 10 is about `A *_C A` for a *separable MF* algebra `A`.  The
two things it asks of the factor -- countability and the MF property -- are
proved here rather than assumed, so the sentence may be quoted in its general
form and applied with nothing left to supply. -/

/-- **The general symmetric-amalgamation sentence, MF-factor form.**  If every
countable operator-MF group has operator-MF symmetric doubles over every
subgroup, the manuscript's exact residual computation follows.

The application is `hShulman SigmaGroup sigmaBase sigmaGroup_isOperatorMF`:
`Countable SigmaGroup` is found by instance search and the MF hypothesis is
`Sofic/SigmaGroupMF.sigmaGroup_isOperatorMF`. -/
theorem manuscriptExactRadical_of_shulmanSymmetricAmalgamation
    (hShulman : ∀ (G : Type) [Group G] [Countable G] (Γ : Subgroup G),
      IsOperatorMF G → IsOperatorMF (SymmetricDouble G Γ)) :
    signFreeCollapseDefect = signFreePrintedDefect ∧
      actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect ∧
        actualCoronaMFResidual MarkedGroup =
          signFreeCollapseDefect.comap proj :=
  manuscriptExactRadical_of_symmetricDoubleMF
    (hShulman SigmaGroup sigmaBase sigmaGroup_isOperatorMF)

/-- **The general symmetric-amalgamation sentence, residually-finite-factor
form.**  This is the shape the manuscript quotes: residual finiteness of the
vertex group, and no property of the edge group.

`Sofic/SymmetricDoubleMF` shows the conclusion cannot be obtained from the
hypothesis by any exact-model argument -- the double here is not residually
finite and not even `LEF` -- so a proof of this sentence is necessarily
analytic even though its statement is group-theoretic. -/
theorem manuscriptExactRadical_of_shulmanResiduallyFiniteDouble
    (hShulman : ∀ (G : Type) [Group G] [Countable G],
      Group.ResiduallyFinite G → ∀ Γ : Subgroup G,
        IsOperatorMF (SymmetricDouble G Γ)) :
    signFreeCollapseDefect = signFreePrintedDefect ∧
      actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect ∧
        actualCoronaMFResidual MarkedGroup =
          signFreeCollapseDefect.comap proj :=
  manuscriptExactRadical_of_symmetricDoubleMF
    (hShulman SigmaGroup sigmaGroup_residuallyFinite sigmaBase)

/-! ## The input is exactly as strong as the endpoint -/

/-- **The converse of the endpoint wrapper.**  The two radical identities of
the manuscript's conclusion give operator MF of the symmetric double back.

The defect equality `D_coll = D/⟨w⟩` is the first conjunct of the conclusion,
and it is what makes `terminalEquiv` --- an isomorphism of the quotient by the
*printed* defect --- usable against
`AmalgamMFTrace.exactRadical_iff_isOperatorMF_symmetricDouble`, which reads the
quotient by the *collapse* defect.  `QuotientGroup.quotientMulEquivOfEq`
transports it across. -/
theorem isOperatorMF_symmetricDouble_of_manuscriptExactRadical
    (hdef : signFreeCollapseDefect = signFreePrintedDefect)
    (hres : actualCoronaMFResidual MarkedGroup =
      signFreeCollapseDefect.comap proj) :
    IsOperatorMF (SymmetricDouble SigmaGroup sigmaBase) :=
  (AmalgamMFTrace.exactRadical_iff_isOperatorMF_symmetricDouble
    (G := SigmaGroup) (Γ := sigmaBase)
    ((QuotientGroup.quotientMulEquivOfEq hdef).trans terminalEquiv)).mp hres

/-- **The last input and the manuscript's endpoint are equivalent.**

Forward is `manuscriptExactRadical_of_symmetricDoubleMF`, the wrapper with the
presentation calculation discharged.  Backward is
`isOperatorMF_symmetricDouble_of_manuscriptExactRadical`.

So the analytic input is not merely sufficient: it is necessary.  Any route to
the exact MF-radical computation proves operator MF of `Σ *_B Σ` on the way,
and there is no weaker hypothesis to look for. -/
theorem manuscriptExactRadical_iff_symmetricDoubleMF :
    IsOperatorMF (SymmetricDouble SigmaGroup sigmaBase) ↔
      (signFreeCollapseDefect = signFreePrintedDefect ∧
        actualCoronaMFResidual SignFreeQuotient = signFreePrintedDefect ∧
          actualCoronaMFResidual MarkedGroup =
            signFreeCollapseDefect.comap proj) :=
  ⟨manuscriptExactRadical_of_symmetricDoubleMF,
    fun h ↦ isOperatorMF_symmetricDouble_of_manuscriptExactRadical h.1 h.2.2⟩

/-! ## The state of the pair, in one proposition -/

/-- **Everything the repository proves about the pair `(Σ, B)` that bears on
the last input.**

The factor is operator MF and residually finite; the edge group is a proper,
non-normal subgroup of it; and the double is not residually finite.  Conjuncts
one and three say the pair is not the `Γ = ⊤` pair the general sentence is
refuted at; conjunct four says the amalgam is not a collapsed one; conjunct
five says the exact route to the input is closed, so conjunct two cannot be
pushed forward to the double by any finite-model argument.

What is *not* in this list is the input itself, and that is the honest reading
of the file: the pair passes every test the library can run, and the remaining
statement is the C⋆-theorem. -/
theorem symmetricDoubleShulman_state :
    IsOperatorMF SigmaGroup ∧
      Group.ResiduallyFinite SigmaGroup ∧
        sigmaBase ≠ ⊤ ∧
          ¬ sigmaBase.Normal ∧
            ¬ Group.ResiduallyFinite (SymmetricDouble SigmaGroup sigmaBase) :=
  ⟨sigmaGroup_isOperatorMF, sigmaGroup_residuallyFinite, sigmaBase_ne_top,
    sigmaBase_not_normal, SymmetricDoubleMF.symmetricDouble_not_residuallyFinite⟩

end

end TerminalQuotientPresentation
end GroupApproximation
