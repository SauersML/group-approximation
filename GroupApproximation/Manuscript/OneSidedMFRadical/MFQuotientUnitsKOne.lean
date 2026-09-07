import GroupApproximation.Manuscript.OneSidedMFRadical.MFQuotientUnitsUnconditional
import GroupApproximation.KOne.AlgebraicKOne

/-!
# `thm:mf-quotient-units` with the quotient named `K₁(R)`

`non_mf_groups_exist.tex`, Theorem `thm:mf-quotient-units`:

> Let `R` be a countable purely infinite simple ring and let `n ≥ 1`.  Then every
> homomorphism from `GL_n(R)` to an MF group factors uniquely through the
> canonical map `GL_n(R) → K_1(R)`, and `K_1(R)`, a countable abelian group, is
> MF.  Equivalently, the intersection `N_n` of the kernels of all homomorphisms
> from `GL_n(R)` to MF groups is `[GL_n(R),GL_n(R)]`, and
> `GL_n(R)/N_n ≅ K_1(R)`.

`MFQuotientUnits.lean` proves the "equivalently" half with the quotient stated
as *"some countable abelian MF group with an isomorphism onto it"*, and its own
docstring records what that costs: `K_1(R)` is never named, so the printed
identification is not carried, and neither is the printed first sentence about
factoring through `κ`.  `KOne/AlgebraicKOne.lean` now supplies `K_1(R)` and `κ`
for an arbitrary ring, so both can be stated as printed.

## What this module adds

* `AGPUnitKappa` — Ara--Goodearl--Pardo, Theorem 2.4, restated about the tree's
  own `κ : Rˣ → K₁(R)` instead of an abstract group.  It is **weaker** than the
  `AGPUnitK1` it replaces: that proposition also had to assume the target was
  countable and abelian, and those are now theorems
  (`AlgebraicK.algebraicKOneCommGroup`, `AlgebraicK.algebraicKOne_countable`).
  `agpUnitK1_of_kappa` shows it still supplies everything `MFQuotientUnits.lean`
  consumes.
* `PrintedMFQuotientUnitsKOne` — the printed theorem at `n = 1`, with the
  quotient identified with `K_1(R)` on the nose **and** the printed unique
  factorization through `κ`, which no declaration carried before.
* `PrintedMFQuotientUnitsKOneAllRanks` — the same at every `n ≥ 1`, with the
  quotient identified with `K_1(M_n(R))`.

## The one printed step that remains a citation

The printed proof reduces `n ≥ 2` to `n = 1` by two moves: `M_n(R)` is again
countable purely infinite simple (`AGPMatrixReduction`, cited), and
`K_1(M_n(R)) ≅ K_1(R)` **by Morita invariance**.  The second is `MoritaKOne`
below, and it is stated, not proved.  It is not out of reach — `K₁(M_n(R))` is
the colimit of `GL_m(M_n(R)) ≅ GL_{mn}(R)`, a cofinal subsystem of the colimit
defining `K₁(R)`, and the flattening `StableWhitehead.twoBlockUnitEquiv` is the
`m = 2` case of the isomorphism that argument needs — but it is a cofinality
argument about direct limits and it is not attempted here.

Because the ranks are only ever compared through that citation, this module
states the general-rank theorem at `K_1(M_n(R))` and keeps `MoritaKOne` as a
separate named hypothesis of the version that says `K_1(R)`.  Stating the
general-rank theorem at `K_1(M_n(R))` and calling it the printed statement would
be a weakening dressed as a proof: the printed conclusion says `K_1(R)`.
-/

namespace GroupApproximation
namespace MFQuotientUnitsKOne

open Manuscript.OneSidedMFRadical
open MFQuotientUnits
open AlgebraicK

/-! ### The Ara--Goodearl--Pardo input, restated about `κ` -/

/-- **Ara--Goodearl--Pardo, Theorem 2.4**, about the canonical `κ : Rˣ → K₁(R)`
of `KOne/AlgebraicKOne.lean`.

Two clauses, where `MFQuotientUnits.AGPUnitK1` has four: that `κ` is surjective
and that its kernel is the commutator subgroup.  Countability and commutativity
of the target are no longer assumed, because `K₁(R)` is proved to have both. -/
def AGPUnitKappa : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    Function.Surjective (kappa R) ∧ (kappa R).ker = commutator Rˣ

/-- The restated input supplies the abstract one: take the abstract group to be
`K₁(R)` itself. -/
theorem agpUnitK1_of_kappa (h : AGPUnitKappa) : AGPUnitK1 := by
  intro R _ _ hR
  obtain ⟨hsurj, hker⟩ := h R hR
  exact ⟨AlgebraicKOne R, inferInstance, inferInstance, kappa R, hsurj, hker⟩

/-! ### The printed theorem at `n = 1` -/

/-- **`thm:mf-quotient-units` at `n = 1`, exactly as printed.**

Four clauses, in the printed order: the unique factorization through `κ`, that
`K_1(R)` is MF, that the MF-hom kernel is the commutator subgroup, and that the
quotient by it is `K_1(R)`. -/
def PrintedMFQuotientUnitsKOne : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    (∀ (M : Type) [Group M], IsOperatorMF M → ∀ f : Rˣ →* M,
        ∃! g : AlgebraicKOne R →* M, g.comp (kappa R) = f) ∧
      IsOperatorMF (AlgebraicKOne R) ∧
      mfHomKernel Rˣ = commutator Rˣ ∧
      Nonempty (Rˣ ⧸ mfHomKernel Rˣ ≃* AlgebraicKOne R)

/-- **The printed theorem at `n = 1`, from the Ara--Goodearl--Pardo inputs.**

`thm:full-defect-ring`'s rank-two form is discharged, not assumed, as in
`MFQuotientUnitsUnconditional.lean`; the countable-abelian-is-MF sentence is
discharged by `countableAbelianMF`. -/
theorem printedMFQuotientUnitsKOne_of_agp
    (hK : AGPUnitKappa) (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) :
    PrintedMFQuotientUnitsKOne := by
  intro R _ _ hR
  obtain ⟨hsurj, hker⟩ := hK R hR
  -- The MF-hom kernel is the commutator subgroup, hence the kernel of `κ`.
  have hcomm : mfHomKernel Rˣ = commutator Rˣ :=
    (mfHomKernel_units_eq_commutator
      Manuscript.OneSidedMFRadical.FullDefectRingEJZUnconditional.manuscriptFullComplementaryIdempotentsRankTwoAllCharacteristics
      (agpUnitK1_of_kappa hK) hMM hS1 countableAbelianMF R hR).1
  have hkerEq : mfHomKernel Rˣ = (kappa R).ker := by rw [hcomm, hker]
  -- `K₁(R)` is MF: it is countable and abelian.
  have hMF : IsOperatorMF (AlgebraicKOne R) := countableAbelianMF (AlgebraicKOne R)
  -- The comparison map is the one `κ` induces.
  have he : ∀ u : Rˣ,
      (QuotientGroup.quotientKerEquivOfSurjective (kappa R) hsurj)
        (QuotientGroup.mk u) = kappa R u := fun _ => rfl
  have hsymm : ∀ u : Rˣ,
      (QuotientGroup.quotientKerEquivOfSurjective (kappa R) hsurj).symm
          (kappa R u)
        = (QuotientGroup.mk u : Rˣ ⧸ (kappa R).ker) := by
    intro u
    rw [← he u]
    exact (QuotientGroup.quotientKerEquivOfSurjective (kappa R) hsurj).symm_apply_apply _
  refine ⟨?_, hMF, hcomm, ⟨(QuotientGroup.quotientMulEquivOfEq hkerEq).trans
    (QuotientGroup.quotientKerEquivOfSurjective (kappa R) hsurj)⟩⟩
  intro M _ hM f
  -- Every homomorphism to an MF group kills the MF-hom kernel, hence `ker κ`.
  have hf : (kappa R).ker ≤ f.ker := by
    intro x hx
    rw [← hkerEq] at hx
    exact (mem_mfHomKernel_iff x).mp hx M hM f
  have hval : ∀ u : Rˣ, QuotientGroup.lift (kappa R).ker f hf
      ((QuotientGroup.quotientKerEquivOfSurjective (kappa R) hsurj).symm
        (kappa R u)) = f u := by
    intro u
    rw [hsymm u]
    exact QuotientGroup.lift_mk' _ hf u
  refine ⟨(QuotientGroup.lift (kappa R).ker f hf).comp
      (QuotientGroup.quotientKerEquivOfSurjective (kappa R) hsurj).symm.toMonoidHom,
    ?_, ?_⟩
  · refine MonoidHom.ext fun u => ?_
    exact hval u
  · intro g hg
    refine MonoidHom.ext fun x => ?_
    obtain ⟨u, hu⟩ := hsurj x
    have h1 : g (kappa R u) = f u := DFunLike.congr_fun hg u
    rw [← hu, h1]
    exact (hval u).symm

/-! ### Every rank -/

/-- **`thm:mf-quotient-units` at every `n ≥ 1`**, with the quotient identified
with `K_1(M_n(R))`.

The printed conclusion names `K_1(R)`; reaching it from here is exactly the
printed Morita step, `MoritaKOne`. -/
def PrintedMFQuotientUnitsKOneAllRanks : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ n : ℕ, 1 ≤ n →
      IsOperatorMF (AlgebraicKOne (Matrix (Fin n) (Fin n) R)) ∧
        mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ
            = commutator (Matrix (Fin n) (Fin n) R)ˣ ∧
          Nonempty ((Matrix (Fin n) (Fin n) R)ˣ ⧸
              mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ
            ≃* AlgebraicKOne (Matrix (Fin n) (Fin n) R))

theorem printedMFQuotientUnitsKOneAllRanks_of_agp
    (hMat : AGPMatrixReduction) (hK : AGPUnitKappa)
    (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) :
    PrintedMFQuotientUnitsKOneAllRanks := by
  intro R _ _ hR n hn
  haveI : Countable (Matrix (Fin n) (Fin n) R) := by
    show Countable (Fin n → Fin n → R)
    infer_instance
  obtain ⟨-, hMF, hcomm, hiso⟩ :=
    printedMFQuotientUnitsKOne_of_agp hK hMM hS1
      (Matrix (Fin n) (Fin n) R) (hMat R hR n hn)
  exact ⟨hMF, hcomm, hiso⟩

/-! ### The remaining printed citation -/

/-- **Morita invariance**, the printed "`K_1(M_n(R)) ≅ K_1(R)` by Morita
invariance".

Stated, not proved.  See the module docstring for why it is the only printed
step of `thm:mf-quotient-units` that this development still cites rather than
carries, and for the shape a proof would take. -/
def MoritaKOne : Prop :=
  ∀ (R : Type) [Ring R] (n : ℕ), 1 ≤ n →
    Nonempty (AlgebraicKOne (Matrix (Fin n) (Fin n) R) ≃* AlgebraicKOne R)

/-- **`thm:mf-quotient-units` at every `n ≥ 1`, with the printed `K_1(R)`.**
The Morita step is the printed one and is the single hypothesis separating this
from `PrintedMFQuotientUnitsKOneAllRanks`. -/
def PrintedMFQuotientUnitsKOneAtBaseRing : Prop :=
  ∀ (R : Type) [Ring R] [Countable R], IsPurelyInfiniteSimpleRing R →
    ∀ n : ℕ, 1 ≤ n →
      mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ
          = commutator (Matrix (Fin n) (Fin n) R)ˣ ∧
        Nonempty ((Matrix (Fin n) (Fin n) R)ˣ ⧸
            mfHomKernel (Matrix (Fin n) (Fin n) R)ˣ ≃* AlgebraicKOne R)

theorem printedMFQuotientUnitsKOneAtBaseRing_of_agp
    (hMat : AGPMatrixReduction) (hK : AGPUnitKappa)
    (hMM : AGPMenalMoncasiReduction) (hS1 : AGPStepOne) (hMor : MoritaKOne) :
    PrintedMFQuotientUnitsKOneAtBaseRing := by
  intro R _ _ hR n hn
  obtain ⟨-, hcomm, ⟨e⟩⟩ :=
    printedMFQuotientUnitsKOneAllRanks_of_agp hMat hK hMM hS1 R hR n hn
  obtain ⟨m⟩ := hMor R n hn
  exact ⟨hcomm, ⟨e.trans m⟩⟩

end MFQuotientUnitsKOne
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.MFQuotientUnitsKOne.agpUnitK1_of_kappa
#audit_axioms GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOne_of_agp
#audit_axioms GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOneAllRanks_of_agp
#audit_axioms GroupApproximation.MFQuotientUnitsKOne.printedMFQuotientUnitsKOneAtBaseRing_of_agp
