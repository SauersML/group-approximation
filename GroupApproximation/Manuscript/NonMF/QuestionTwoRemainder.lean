import GroupApproximation.Sofic.NormalKazhdanMFRadical
import GroupApproximation.Sofic.ActualCoronaMFRadical
import GroupApproximation.Sofic.TorsionFreeFiniteNormalLimit
import GroupApproximation.Kazhdan.ShalomFinitePresentation
import Mathlib.Algebra.Group.PUnit
import Mathlib.Algebra.Group.Torsion
import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# The torsion-free obstruction reduction, and the sharp form of "nontrivial"

Earlier manuscript revisions asked for a torsion-free finitely presented
non-MF group and printed the following reduction:

> For torsion-free groups, Theorem~\ref{thm:criterion} gives no obstruction
> because every finite subgroup is trivial, while Theorem~\ref{thm:normal-kazhdan}
> does apply.  What remains is group-theoretic: a torsion-free finitely
> presented group whose subgroup `N_conj` contains a *nontrivial* normal
> property-(T) subgroup.

## What this file adds, and to what

`Sofic.QuestionTwoReduction` already proves the obstruction half:
`not_isOperatorMF_of_nontrivial_normal_kazhdan_defect` says that a countable
group whose compression defect contains a nontrivial normal property-`(T)`
subgroup is not operator-MF, and `bot_hasKazhdanPropertyT` together with
`obstruction_vacuous_at_bot` records that the conclusion at `K = ⊥` is
`bot_le`.  **That module is deliberately not imported here.**  Neither file has
been elaborated yet, and a hard dependency between two uncompiled modules makes
one red module hide the other; the only thing this file would take from it is
the one-line `bot_hasKazhdanPropertyT`, which is
`Shalom.hasKazhdanPropertyT_of_subsingleton` and is spelled out again below as
one clause of a three-clause bundle.  When both are green the import can be
added and the clause deleted; until then the two files stand or fall
separately.

That module's own ledger note names what it does not reach: "the printed
clause is a claim about what REMAINS, whose other half is `LI.07` and `LI.08`
rather than anything here".  This file supplies that other half and one
sharpening.

* `manuscriptQuestionTwoGroupTheoreticRemainder` is the printed sentence
  entire, with the torsion-freeness in the hypotheses where the print puts it.
  It returns the criterion clause — every finite subgroup of `H` is trivial,
  which is `LI.07` at `finiteSubgroup_eq_bot_of_isMulTorsionFree`, quoted and
  not reproved — alongside the normal-Kazhdan clause, in the printed order, and
  in the manuscript's own radical language: `K` lies in the literal
  genuine-corona MF radical, that radical is therefore not trivial, and `H` is
  not CDE-MF.  This is the formal analytic implication used by the manuscript's
  present paper-level torsion-free construction.
* `exists_isCDEOperatorMF_with_bot_normalKazhdan` sharpens
  `obstruction_vacuous_at_bot` from "the conclusion is empty" to "the
  hypotheses have no consequence".  There is a countable torsion-free finitely
  presented group carrying a Kazhdan compression core and a normal
  property-`(T)` subgroup of its compression defect which **is** CDE-MF: the
  trivial group with `K = ⊥`.  A vacuous conclusion and a realized negation are
  different facts, and it is the second that makes *nontrivial* load-bearing
  rather than merely unhelpful.
* `bot_satisfies_normalKazhdanHypotheses` states the two clauses the prose of
  the companion module asserts but does not state — `⊥` is normal and `⊥` lies
  in the defect — next to the property-`(T)` clause it does state.

**This module does not construct the group.**  The manuscript now supplies the
group-theoretic input at paper level from Fournier-Facio, Hull, and Osin, but
that small-cancellation argument is not formalized in Lean.  The declarations
below retain the exact formal boundary: once such a compression datum and
nontrivial normal Kazhdan subgroup are supplied, the group is not MF.

Finite presentation is carried as a hypothesis and returned as a conclusion, and
no other clause uses it.  That is deliberate and is what the printed sentence
said: finite presentation belongs to the group-theoretic profile,
not to the obstruction being invoked, so it is part of the profile the
conclusion delivers rather than an input the proof consumes.  Returning it is
also what keeps the binder from reading as an unused hypothesis, which is a
different and worse defect than an honest one.  The manuscript's standing
convention makes every group countable, so `[Countable H]` is convention rather
than an added hypothesis.

Every declaration states its binders after the colon, as the badged manuscript
forms do; the zero-input gate rejects header binders.
-/

namespace GroupApproximation
namespace ManuscriptNonMF

/-! ## The torsion-free reduction, torsion-freeness included -/

/-- **The manuscript's torsion-free obstruction reduction.**

Let `H` be a countable torsion-free finitely presented group carrying a Kazhdan
compression datum, and let `K ⊴ H` be a **nontrivial** property-`(T)` subgroup of
the compression defect `N_conj`.  Then, in the printed order:

* `thm:criterion` gives no obstruction, because every finite subgroup of `H` is
  trivial — this is `LI.07`, quoted at `finiteSubgroup_eq_bot_of_isMulTorsionFree`
  and not reproved here;
* `thm:normal-kazhdan` does apply: `K` lies in the literal genuine-corona MF
  radical of `H`;
* that radical is therefore not trivial;
* `H` is finitely presented — the hypothesis returned, because it is part of the
  profile under discussion and not an input to the obstruction; and
* `H` is not MF in the Carrión--Dadarlat--Eckhardt sense.

So a group with this profile is torsion-free, finitely presented, and non-MF.
The manuscript now constructs the required profile at paper level; nothing in
this file formalizes that small-cancellation construction.

`Sofic.QuestionTwoReduction.not_isOperatorMF_of_nontrivial_normal_kazhdan_defect`
proves the last clause for `IsOperatorMF` without the torsion hypotheses; the
point of this statement is the first clause and the printed assembly, not the
last. -/
theorem manuscriptQuestionTwoGroupTheoreticRemainder :
    ∀ {Gamma : Type} {H : Type} [Group Gamma] [Group H] [Countable H]
      [IsMulTorsionFree H] [Group.IsFinitelyPresented H]
      (C : KazhdanCompressionCore Gamma H) (K : Subgroup H) [K.Normal],
      HasKazhdanPropertyT.{0, 0} K →
      K ≤ C.defectNormal →
      K ≠ ⊥ →
      (∀ F : Subgroup H, Finite F → F = ⊥) ∧
        K ≤ actualCoronaMFResidual H ∧
        actualCoronaMFResidual H ≠ ⊥ ∧
        Group.IsFinitelyPresented H ∧
        ¬ IsCDEOperatorMF H := by
  intro Gamma H _ _ _ _ hfp C K _ hT hK hne
  -- `thm:criterion` is vacuous: this is `LI.07`, quoted and not reproved
  have hcrit : ∀ F : Subgroup H, Finite F → F = ⊥ := by
    intro F hF
    haveI := hF
    exact finiteSubgroup_eq_bot_of_isMulTorsionFree H F
  -- `thm:normal-kazhdan` does apply
  have hres : K ≤ actualCoronaMFResidual H := by
    rw [actualCoronaMFResidual_eq_coronaMFResidual]
    exact C.normalKazhdan_le_coronaMFResidual K hT hK
  -- and it says something, because `K` is nontrivial
  have hbot : actualCoronaMFResidual H ≠ ⊥ := by
    intro hb
    exact hne (le_bot_iff.mp (hres.trans (le_of_eq hb)))
  have hmf : ¬ IsCDEOperatorMF H := by
    intro hMF
    exact hbot (isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hMF)
  exact ⟨hcrit, hres, hbot, hfp, hmf⟩

/-! ## Why *nontrivial* is load-bearing, sharply

`QuestionTwoReduction.obstruction_vacuous_at_bot` shows the conclusion at
`K = ⊥` is `bot_le`.  The two declarations below complete that observation:
the rest of the hypothesis package is met by `⊥` in every group, and the
profile it leaves behind is realized by an MF group, so nothing at all follows
from the package with `K ≠ ⊥` dropped. -/

/-- **`⊥` meets every hypothesis of `thm:normal-kazhdan` except nontriviality.**

In every group carrying a Kazhdan compression core, the trivial subgroup is
normal, has property `(T)` vacuously because `Unique (⊥ : Subgroup H)`, and is
contained in `N_conj` by `bot_le`.  The companion module states the middle
clause alone, as `QuestionTwoReduction.bot_hasKazhdanPropertyT`, and asserts the
outer two in prose; this states all three against a compression core, which is
where the hypothesis package actually lives.  The middle clause is the same
one-line proof, repeated rather than imported for the build-independence reason
in the module docstring. -/
theorem bot_satisfies_normalKazhdanHypotheses :
    ∀ {Gamma : Type} {H : Type} [Group Gamma] [Group H]
      (C : KazhdanCompressionCore Gamma H),
      (⊥ : Subgroup H).Normal ∧
        HasKazhdanPropertyT.{0, 0} (⊥ : Subgroup H) ∧
        (⊥ : Subgroup H) ≤ C.defectNormal := by
  intro Gamma H _ _ _
  exact ⟨Subgroup.normal_bot, Shalom.hasKazhdanPropertyT_of_subsingleton, bot_le⟩

/-- The Kazhdan compression core of the trivial group.  Every field is
`Subsingleton.elim` or the vacuous property `(T)`; it exists only to be the
carrier of `exists_isCDEOperatorMF_with_bot_normalKazhdan`. -/
def trivialCompressionCore : KazhdanCompressionCore PUnit.{1} PUnit.{1} where
  iota := MonoidHom.id PUnit.{1}
  t := 1
  c := 1
  kazhdan := Shalom.hasKazhdanPropertyT_of_subsingleton
  compresses := fun gamma ↦ ⟨gamma, Subsingleton.elim _ _⟩
  comm_c := fun _ ↦ Commute.all _ _

/-- The trivial group is CDE-MF: its literal genuine-corona radical is `⊥`
because it is its only subgroup. -/
theorem isCDEOperatorMF_punit : IsCDEOperatorMF PUnit.{1} :=
  isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mpr (Subsingleton.elim _ _)

/-- **The hypothesis package minus nontriviality has no MF consequence.**

There is a countable, torsion-free, finitely presented group carrying a Kazhdan
compression core and a normal property-`(T)` subgroup of its compression defect
which is nevertheless CDE-MF.  It is the trivial group with `K = ⊥`, and it
satisfies every hypothesis of `manuscriptQuestionTwoGroupTheoreticRemainder`
except `K ≠ ⊥`.

This is the sharp form of the deleted sentence, and it is strictly more than
`QuestionTwoReduction.obstruction_vacuous_at_bot`: that theorem says the
conclusion at `⊥` is empty, this one says the hypotheses at `⊥` are consistent
with the negation of the conclusion the nontrivial case delivers.

The witness is deliberately the smallest one.  Exhibiting a *nontrivial*
torsion-free finitely presented MF group with this profile would say the same
thing more loudly, but the printed sentence is refuted at the trivial group
already, and a larger witness would need an MF proof this file does not have. -/
theorem exists_isCDEOperatorMF_with_bot_normalKazhdan :
    ∃ (Gamma : Type) (H : Type) (_ : Group Gamma) (_ : Group H) (_ : Countable H)
      (_ : IsMulTorsionFree H) (_ : Group.IsFinitelyPresented H)
      (C : KazhdanCompressionCore Gamma H) (K : Subgroup H),
      K.Normal ∧ HasKazhdanPropertyT.{0, 0} K ∧ K ≤ C.defectNormal ∧
        IsCDEOperatorMF H :=
  ⟨PUnit.{1}, PUnit.{1}, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, trivialCompressionCore, ⊥, Subgroup.normal_bot,
    Shalom.hasKazhdanPropertyT_of_subsingleton, bot_le, isCDEOperatorMF_punit⟩

end ManuscriptNonMF
end GroupApproximation
