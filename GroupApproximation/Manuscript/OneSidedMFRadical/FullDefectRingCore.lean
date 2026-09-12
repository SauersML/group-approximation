import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Sofic.FullRadicalClosureProperties
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# `thm:full-defect-ring`: the MF endpoint of a saturated printed defect

`non_mf_groups_exist.tex`, Theorem `thm:full-defect-ring` (full complementary
idempotents), last step of its proof:

> By Theorem~`thm:compression-criterion` with `K = G`, every homomorphism from
> `G` to an MF group is trivial.

This module isolates that last step.  Nothing here is about rings: the input
is a countable group `G`, a subgroup `L` with property `(T)`, property `(T)`
for `G` itself, and the saturation `𝔇_G(L) = ⊤` of the printed defect; the
output is the full MF radical and its two formal consequences.  The
ring-theoretic work of `thm:full-defect-ring` — the compressor `u`, the
centralizer element `c`, and the normal generation of `EL_n(R)` by
`d = [ucu⁻¹, ℓ]` under fullness of `1 - st` — is what supplies the saturation
hypothesis, and lives in `GroupApproximation.Leavitt.OneSidedCompressor*`.

Splitting the proof here has a purpose beyond tidiness.  The printed proof
runs the compression criterion at `K = G` exactly once, and every later clause
of the theorem and of its two corollaries is a consequence of the *conclusion*
of that single application.  So the saturation hypothesis is the only interface
between the ring calculation and the operator-algebraic conclusion, and the
declaration below is where that interface is named.

The module also records the countability of `EL_ι(R)` over a countable ring,
which is the standing hypothesis of `thm:full-defect-ring` ("Let `R` be a
countable unital associative ring") in the form the compression criterion asks
for it.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical
namespace FullDefectRing

/-! ## Countability of the elementary group -/

section Countability

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- The entries of an elementary matrix, as a plain function.  An element of
`EL_ι(R)` is a unit of `M_ι(R)`, and a unit is determined by its value, so
this map is injective. -/
private def entries (g : elementaryGroup ι R) : ι → ι → R :=
  fun i j ↦ ((g : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j

private theorem entries_injective :
    Function.Injective (entries (ι := ι) (R := R)) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact congrFun (congrFun h i) j

/-- **`EL_ι(R)` is countable when `R` is.**  This is the countability
hypothesis of `thm:full-defect-ring`, transported from the coefficient ring to
the group: a matrix over `ι` is a function on the finite set `ι × ι`, and a
unit of the matrix ring is determined by its underlying matrix. -/
theorem countable_elementaryGroup [Countable R] :
    Countable (elementaryGroup ι R) :=
  entries_injective.countable

end Countability

/-! ## The last step of the printed proof -/

/-- **The saturated printed defect kills every MF target.**

The hypotheses are the ones the printed proof has in hand when it invokes
`thm:compression-criterion`: `G` is countable, `L ≤ G` has property `(T)`, `G`
has property `(T)`, and the printed defect `𝔇_G(L)` is everything.  The four
conclusions are, in order,

* `Rad_MF(G) = G` in the manuscript's literal natural-dimension reading;
* the same in the basis-free reading;
* every homomorphism from `G` to an MF group is trivial; and
* `G` itself is not MF, as soon as it is nontrivial.

The nontriviality of `G` is a hypothesis of the fourth clause rather than of
the whole statement because the first three hold vacuously in the trivial
group, and because `thm:full-defect-ring` as printed asserts only the third:
the failure of MF-ness is the corollary a reader draws from it. -/
def SaturatedPrintedDefectRadical : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L → HasKazhdanPropertyT.{0, 0} G →
      printedDefect L = ⊤ →
        manuscriptCoronaMFResidual G = ⊤ ∧
          actualCoronaMFResidual G = ⊤ ∧
          (∀ (M : Type) [Group M], IsOperatorMF M →
            ∀ (f : G →* M) (x : G), f x = 1) ∧
          (Nontrivial G → ¬ IsCDEOperatorMF G)

/-- **The last step of the printed proof of `thm:full-defect-ring`, proved.**

Third clause of `manuscriptOneSidedCompressionCriterion` for the radical,
`manuscriptCoronaMFResidual_eq_actualCoronaMFResidual` for the second reading,
`manuscriptFullRadicalKillsMFTargets` for the triviality of MF-target
homomorphisms, and
`not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top` for the failure of
MF-ness.  No new mathematics: the module exists to name the interface. -/
theorem manuscriptSaturatedPrintedDefectRadical :
    SaturatedPrintedDefectRadical := by
  intro G _ _ L hL hG hD
  have hman : manuscriptCoronaMFResidual G = ⊤ :=
    (manuscriptOneSidedCompressionCriterion (G := G) L hL).2.2 hG hD
  have hact : actualCoronaMFResidual G = ⊤ := by
    rwa [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual] at hman
  refine ⟨hman, hact, ?_, ?_⟩
  · intro M _ hM f x
    exact manuscriptFullRadicalKillsMFTargets (G := G) (M := M) hman hM f x
  · intro hnt
    haveI : Nontrivial G := hnt
    exact not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top hact

end FullDefectRing
end OneSidedMFRadical
end Manuscript
end GroupApproximation

open GroupApproximation

#audit_closed_axioms
  Manuscript.OneSidedMFRadical.FullDefectRing.manuscriptSaturatedPrintedDefectRadical
