import GroupApproximation.KOne.MoritaKOne
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsMatrixReduction
import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientCanonicalKOne

/-!
# The printed Morita step of `thm:mf-quotient-units`, discharged

`non_mf_groups_exist.tex`, line 1182--1184, the first sentence of the proof of
`thm:mf-quotient-units`:

> The ring `M_n(R)` is again countable, purely infinite, and
> simple~\cite[Corollary~1.7]{AGP}, and `K_1(M_n(R)) ≅ K_1(R)` by
> Morita invariance, so it suffices to treat `n=1`.

`MFQuotientUnitsKOne.lean` states the second clause as the hypothesis
`MoritaKOne`, and its module docstring records that this is the one printed step
of that theorem which the development cites rather than carries.
`KOne/MoritaKOne.lean` now proves it for an arbitrary unital ring and every
`n ≥ 1`, so this module discharges the hypothesis and restates without it the
two theorems that took it.

## Relation to `MFQuotientCanonicalKOne.lean`

The printed *conclusion* `PrintedMFQuotientUnitsKOneAtBaseRing` is already
unconditional: `manuscriptMFQuotientUnitsKOneAtBaseRing` reaches it by a
different route, comparing `GL_n(R)` with `K_1(R)` through the rank-`n` map
`matrixKappa` instead of through `K_1(M_n(R))`.  What was missing was the
printed *sentence*: the Morita isomorphism itself, which no declaration
carried.  `moritaKOne` carries it, and
`moritaKOneEquiv_matrixKappa` records that the two routes agree -- the Morita
identification composed with the printed `κ` of the matrix ring is the tree's
own canonical comparison map `matrixKappa R n`.
-/

namespace GroupApproximation
namespace MFQuotientUnitsKOne

open MFQuotientUnits

/-- **Morita invariance for `K₁`**, the printed step, proved.

`AlgebraicK.morita_algebraicKOne` builds the isomorphism from the flattening
`GL_m(M_n(R)) ≅ GL_{mn}(R)`, the cofinality of `m ↦ m n` in `ℕ`, and the
correspondence of elementary subgroups. -/
theorem moritaKOne : MoritaKOne := by
  intro R _ n hn
  exact AlgebraicK.morita_algebraicKOne R n hn

/-- **The Morita identification is the one the printed proof uses**: composed
with the printed `κ : (M_n(R))^× → K_1(M_n(R))` it is `matrixKappa R n`, the
canonical map `GL_n(R) → K_1(R)` that `MFQuotientCanonicalKOne.lean` compares
against.  So the reduction to `n = 1` identifies the comparison maps, not merely
the groups. -/
theorem moritaKOneEquiv_matrixKappa {R : Type} [Ring R] (n : ℕ) (hn : 1 ≤ n)
    (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    AlgebraicK.moritaKOneEquiv R n hn
        (AlgebraicK.kappa (Matrix (Fin n) (Fin n) R) u)
      = matrixKappa R n u :=
  AlgebraicK.moritaKOneEquiv_kappa R n hn u

/-- **`thm:mf-quotient-units` at every `n ≥ 1` with the printed `K_1(R)`**, from
the Ara--Goodearl--Pardo inputs alone: the Morita step is discharged, not
assumed. -/
theorem printedMFQuotientUnitsKOneAtBaseRing_of_agpNoMorita
    (hMat : AGPMatrixReduction) (hK : AGPUnitKappa)
    (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) :
    PrintedMFQuotientUnitsKOneAtBaseRing :=
  printedMFQuotientUnitsKOneAtBaseRing_of_agp hMat hK hMM hS1 moritaKOne

/-- The same from the three inputs that remain after
`MFQuotientUnitsMatrixReduction.lean` discharges `AGPMatrixReduction`. -/
theorem printedMFQuotientUnitsKOneAtBaseRing_of_agpThreeNoMorita
    (hK : AGPUnitKappa) (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) :
    PrintedMFQuotientUnitsKOneAtBaseRing :=
  printedMFQuotientUnitsKOneAtBaseRing_of_agpThree hK hMM hS1 moritaKOne

end MFQuotientUnitsKOne
end GroupApproximation

/-! ### Axiom audit -/

#audit_closed_axioms GroupApproximation.MFQuotientUnitsKOne.moritaKOne
#audit_axioms GroupApproximation.MFQuotientUnitsKOne.moritaKOneEquiv_matrixKappa
#audit_axioms
  GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOneAtBaseRing_of_agpNoMorita
#audit_axioms
  GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOneAtBaseRing_of_agpThreeNoMorita
