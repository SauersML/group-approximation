import GroupApproximation.Manuscript.OneSidedMFRadical.LeavittMFQuotientKhanhThanhFree
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientCanonicalKOne

/-!
# `cor:leavitt-mf-quotient`, sentence by sentence

`non_mf_groups_exist.tex`, Corollary `cor:leavitt-mf-quotient` (tex lines
1247--1254) and its proof (tex lines 1256--1268):

> Let `k` be a countable field, let `d ≥ 2`, let `R = L_k(1,d)`, and let
> `H = R^×`.  Then `H ≅ GL_d(R)`, and under this identification
> `Rad_MF(H) = [H,H] = EL_d(R)` and `H/EL_d(R) ≅ K_1(R) ≅ k^×/(k^×)^{d-1}`.

One carrier per printed sentence, each quoting its sentence and each proved
from what is already on the tree.  Every carrier here is unconditional; the
binders are the ordinary mathematical ones, the field, its countability, the
arity and `2 ≤ d`.

## What is new here

`H/EL_d(R) ≅ K_1(R)` — the corollary's second display, and the one clause the
existing Leavitt modules explicitly do **not** carry.
`Manuscript/OneSidedMFRadical/LeavittMFQuotientGeneral.lean` records that "the
identification of the quotient with `K₁(R)` and with `k^×/(k^×)^{d-1}` is *not*
carried", and `LeavittMFQuotientKhanhThanhFree.lean` repeats it.  That was
accurate when those modules were written.  It is no longer, because the two
halves now exist and only had to be put together:

* `MFQuotientCanonicalKOne.manuscriptMFQuotientUnitsKOneAtBaseRing` identifies
  `GL_n(S)/Rad_MF` with `K_1(S)` for every countable purely infinite simple `S`
  and every `n ≥ 1`, with no Ara--Goodearl--Pardo and no Morita input;
* `AryLeavitt.isPurelyInfiniteSimpleRing` says `L_k(1,d)` is such an `S`, for
  every field and every `d ≥ 2`.

Taking `S = L_k(1,d)` and `n = d` gives the printed display.  The *second*
isomorphism, `K_1(R) ≅ k^×/(k^×)^{d-1}`, the other half of the Khanh--Thanh
citation, is not stated in this module.  It is proved in
`LeavittKOneFormulaSentences`, which also states the corollary with every clause
(`manuscriptLeavittMFQuotientFull`).

## Why the quotient is stated three ways

The corollary asserts `Rad_MF(H) = [H,H] = EL_d(R)` before it names the
quotient, so `H/Rad_MF(H)`, `H/[H,H]` and `H/EL_d(R)` are the *same* group and
the displayed isomorphism is one statement, not three.  It is recorded at
`Rad_MF` and at the commutator subgroup, where the normality instance is found
by typeclass search, and once literally at `EL_d(R)`, where normality has to be
supplied by hand from `RankNElimination.elementaryGroup_normal_of_division`.

## The Khanh--Thanh sentence

The printed proof cites Khanh--Thanh for two things.  The one the chain
consumes, `[GL_d(R), GL_d(R)] ≤ EL_d(R)`, is a theorem —
`LeavittMFQuotientGeneral.printedKhanhThanhCommutatorInElementary`, from pure
infiniteness alone, with no reference to the Leavitt presentation.  The other,
`K_1(R) ≅ k^×/(k^×)^{d-1}`, is `LeavittKOneFormulaSentences.manuscriptLeavittKOneFormula`,
from `KhanhThanhDiagonal.scalarSurjective_holds` and `LeavittKOneFormula.scalarKernel`.
-/

namespace GroupApproximation
namespace LeavittMFQuotientSentences

open AryLeavitt
open Manuscript.OneSidedMFRadical
open Manuscript.OneSidedMFRadical.LeavittMFQuotientGeneral
open MFQuotientUnits

noncomputable section

variable (k : Type) [Field k] [Countable k] (d : ℕ)

/-! ## Pure infiniteness, the input the corollary inherits from the theorem -/

omit [Countable k] in
/-- `L_k(1,d)` is purely infinite simple, which is what
`thm:mf-quotient-units` asks of its ring; countability of `k` enters only where
the theorem is applied. -/
theorem isPurelyInfiniteSimpleRing_aryLeavitt (hd : 2 ≤ d) :
    IsPurelyInfiniteSimpleRing (AryLeavittAlgebra k d) :=
  AryLeavitt.isPurelyInfiniteSimpleRing k d hd

/-! ## Printed sentence 1 -/

omit [Countable k] in
/-- **Printed sentence 1.**

> The maps `x ↦ (t_1x, …, t_dx)` and `(y_1, …, y_d) ↦ Σ_i s_i y_i` are mutually
> inverse isomorphisms of right `R`-modules between `R` and `R^d`, so
> `R ≅ M_d(R)` and `H ≅ GL_d(R)`.

The consumed conclusion, `H ≅ GL_d(R)`, at every field and every `d ≥ 2`.  The
two displayed formulas themselves are pinned at `d = 2` by
`UniversalLeavitt.manuscriptSentence_rightModuleSelfSimilarity`; the
`d`-ary isomorphism below is the one the rest of the proof uses. -/
theorem manuscriptSentence_unitsEquivGL :
    Nonempty ((AryLeavittAlgebra k d)ˣ ≃*
      (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) :=
  ⟨unitsEquivGL k d⟩

/-! ## Printed sentence 2 -/

/-- **Printed sentence 2.**

> Theorem `thm:mf-quotient-units` identifies the radical with `[H,H]` and the
> quotient with `K_1(R)`.

Both clauses, applied to `R = L_k(1,d)` at rank `d`.  Nothing is assumed: the
theorem is `MFQuotientCanonicalKOne.manuscriptMFQuotientUnitsKOneAtBaseRing`
and its ring hypothesis is `AryLeavitt.isPurelyInfiniteSimpleRing`. -/
theorem manuscriptSentence_theoremIdentifiesRadicalAndQuotient (hd : 2 ≤ d) :
    mfHomKernel (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
        = commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ∧
      Nonempty ((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ⧸
          mfHomKernel (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
        ≃* AlgebraicK.AlgebraicKOne (AryLeavittAlgebra k d)) :=
  MFQuotientUnitsKOne.manuscriptMFQuotientUnitsKOneAtBaseRing
    (AryLeavittAlgebra k d) (isPurelyInfiniteSimpleRing_aryLeavitt k d hd) d
    (by omega)

/-! ## Printed sentence 3, the Khanh--Thanh citation -/

omit [Countable k] in
/-- **Printed sentence 3, the half the printed chain consumes.**

> Khanh--Thanh show that `GL_d(R) = EL_d(R)D_d(k)`, where `D_d(k)` is the
> abelian group of diagonal matrices with entries in `k^×`, which normalizes
> `EL_d(R)`, and that `K_1(R) ≅ k^×/(k^×)^{d-1}`.

Only `[GL_d(R), GL_d(R)] ≤ EL_d(R)` is carried, and it is *proved* rather than
cited: pure infiniteness gives single-sandwich division, Gaussian elimination
puts every invertible matrix in the form `E · diag · F`, and Whitehead's
identity kills the commutators of the diagonal image.  The decomposition
`GL_d(R) = EL_d(R)D_d(k)` itself is not asserted, and neither is
`K_1(R) ≅ k^×/(k^×)^{d-1}`; that one is open. -/
theorem manuscriptSentence_khanhThanhCommutatorInElementary (hd : 2 ≤ d) :
    commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
      ≤ elementaryGroup (Fin d) (AryLeavittAlgebra k d) :=
  printedKhanhThanhCommutatorInElementary k d hd

/-! ## Printed sentence 4 -/

/-- **Printed sentence 4.**

> So `[H,H] ≤ EL_d(R)`, while `EL_d(R) ≤ [H,H]` because every homomorphism from
> `EL_d(R)` to an MF group is trivial (Theorem `thm:full-defect-ring`).

All three clauses: the two inclusions and the printed reason for the second
one.  The middle conjunct is the reason as printed — every homomorphism to an
MF group kills every elementary matrix — and it is where
`thm:full-defect-ring` enters. -/
theorem manuscriptSentence_bothInclusions (hd : 2 ≤ d) :
    commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
        ≤ elementaryGroup (Fin d) (AryLeavittAlgebra k d) ∧
      (∀ x ∈ elementaryGroup (Fin d) (AryLeavittAlgebra k d),
        ∀ (M : Type) [Group M], IsOperatorMF M →
          ∀ f : (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ →* M,
            f x = 1) ∧
      elementaryGroup (Fin d) (AryLeavittAlgebra k d)
        ≤ commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ := by
  obtain ⟨-, hcomm, hiff⟩ := manuscriptLeavittMFQuotientGeneralUnconditional k d hd
  refine ⟨hcomm.le, fun x hx M _ hM f => (hiff x).mp hx M hM f, ?_⟩
  exact hcomm.ge

/-! ## The printed displays -/

/-- **The first printed display**, `Rad_MF(H) = [H,H] = EL_d(R)`.

Both equalities at once, at `GL_d(R)`, for every countable field and every
`d ≥ 2`, with nothing assumed. -/
theorem manuscriptSentence_radicalEqCommutatorEqElementary (hd : 2 ≤ d) :
    mfHomKernel (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
        = commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ∧
      commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
        = elementaryGroup (Fin d) (AryLeavittAlgebra k d) :=
  ⟨(manuscriptSentence_theoremIdentifiesRadicalAndQuotient k d hd).1,
    (manuscriptLeavittMFQuotientGeneralUnconditional k d hd).2.1⟩

omit [Countable k] in
/-- **`EL_d(R)` is normal in `GL_d(R)`**, which the second printed display needs
before it can name the quotient by it.

Not a separate printed sentence: the print takes it from the Khanh--Thanh
decomposition, and it is proved here from single-sandwich division. -/
theorem elementaryGroup_normal (hd : 2 ≤ d) :
    (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal := by
  haveI : NeZero d := ⟨by omega⟩
  exact RankNElimination.elementaryGroup_normal_of_division
    (AryLeavitt.hasSingleSandwichDivision k d hd) ⟨0, by omega⟩

/-- **The second printed display**, `H/EL_d(R) ≅ K_1(R)`, at the commutator
subgroup.

`Rad_MF(H) = [H,H] = EL_d(R)` is the display just above, so this is the printed
isomorphism; the literal spelling at `EL_d(R)` is
`manuscriptSentence_quotientByElementaryIsKOne`. -/
theorem manuscriptSentence_quotientByCommutatorIsKOne (hd : 2 ≤ d) :
    Nonempty ((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ⧸
        commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
      ≃* AlgebraicK.AlgebraicKOne (AryLeavittAlgebra k d)) := by
  obtain ⟨hker, ⟨e⟩⟩ := manuscriptSentence_theoremIdentifiesRadicalAndQuotient k d hd
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans e⟩

/-- **The second printed display, literally**: `H/EL_d(R) ≅ K_1(R)`.

The normality of `EL_d(R)` is supplied by `elementaryGroup_normal`, so the
quotient by the elementary subgroup is the one the corollary prints. -/
theorem manuscriptSentence_quotientByElementaryIsKOne (hd : 2 ≤ d) :
    letI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
      elementaryGroup_normal k d hd
    Nonempty ((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ⧸
        elementaryGroup (Fin d) (AryLeavittAlgebra k d)
      ≃* AlgebraicK.AlgebraicKOne (AryLeavittAlgebra k d)) :=
  letI : (elementaryGroup (Fin d) (AryLeavittAlgebra k d)).Normal :=
    elementaryGroup_normal k d hd
  ⟨(QuotientGroup.quotientMulEquivOfEq
      (manuscriptSentence_radicalEqCommutatorEqElementary k d hd).2.symm).trans
    (manuscriptSentence_quotientByCommutatorIsKOne k d hd).some⟩

/-! ## The corollary, as a closed proposition -/

/-- **`cor:leavitt-mf-quotient`, everything but the last isomorphism.**

> Let `k` be a countable field, let `d ≥ 2`, let `R = L_k(1,d)`, and let
> `H = R^×`.  Then `H ≅ GL_d(R)`, and under this identification
> `Rad_MF(H) = [H,H] = EL_d(R)` and `H/EL_d(R) ≅ K_1(R)`.

The printed statement ends `≅ k^×/(k^×)^{d-1}`.  That last isomorphism is not
asserted here; everything before it is.  The statement with every clause is
`LeavittKOneFormulaSentences.PrintedLeavittMFQuotientFull`, proved by
`manuscriptLeavittMFQuotientFull`. -/
def PrintedLeavittMFQuotientWithKOne : Prop :=
  ∀ (k : Type) [Field k] [Countable k] (d : ℕ), 2 ≤ d →
    Nonempty ((AryLeavittAlgebra k d)ˣ ≃*
        (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ) ∧
      mfHomKernel (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
          = commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ∧
      commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
          = elementaryGroup (Fin d) (AryLeavittAlgebra k d) ∧
      Nonempty ((Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ ⧸
          commutator (Matrix (Fin d) (Fin d) (AryLeavittAlgebra k d))ˣ
        ≃* AlgebraicK.AlgebraicKOne (AryLeavittAlgebra k d))

/-- **The corollary, proved.** -/
theorem manuscriptLeavittMFQuotientWithKOne : PrintedLeavittMFQuotientWithKOne := by
  intro k _ _ d hd
  obtain ⟨hker, hcomm⟩ := manuscriptSentence_radicalEqCommutatorEqElementary k d hd
  exact ⟨manuscriptSentence_unitsEquivGL k d, hker, hcomm,
    manuscriptSentence_quotientByCommutatorIsKOne k d hd⟩

end

end LeavittMFQuotientSentences
end GroupApproximation

/-! ### Axiom audit -/

open GroupApproximation.LeavittMFQuotientSentences

#audit_axioms isPurelyInfiniteSimpleRing_aryLeavitt
#audit_axioms manuscriptSentence_unitsEquivGL
#audit_axioms manuscriptSentence_theoremIdentifiesRadicalAndQuotient
#audit_axioms manuscriptSentence_khanhThanhCommutatorInElementary
#audit_axioms manuscriptSentence_bothInclusions
#audit_axioms manuscriptSentence_radicalEqCommutatorEqElementary
#audit_axioms elementaryGroup_normal
#audit_axioms manuscriptSentence_quotientByCommutatorIsKOne
#audit_axioms manuscriptSentence_quotientByElementaryIsKOne
#audit_closed_axioms GroupApproximation.LeavittMFQuotientSentences.manuscriptLeavittMFQuotientWithKOne
