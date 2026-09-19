import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefectShadow

/-!
# `thm:compression-criterion`, on the printed defect

`non_mf_groups_exist.tex`, Theorem~`thm:compression-criterion` (Theorem~A).

`PrintedDefectShadow` follows the manuscript's proof route: the exact printed
defect lies in the operator-to-Hilbert--Schmidt shadow residual, and the
normal-Kazhdan theorem then puts every normal Kazhdan subgroup of that defect
inside the MF radical.  This module assembles the remaining consequences.

The radical here is `manuscriptCoronaMFResidual`, the manuscript's literal
natural-dimension object: the intersection of the kernels of all
homomorphisms into `∏_n M_{d_n}(ℂ) / ⊕_n M_{d_n}(ℂ)`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/-- **Theorem~A (`thm:compression-criterion`), as one closed proposition.**
The three printed clauses that involve the MF radical, in the printed order:
membership of a normal Kazhdan subgroup of the defect in the radical; a
nontrivial such subgroup obstructing MF-ness; and the saturated case
`𝔇_G(L) = G` forcing a full radical.  The fourth printed clause — that every
finite-dimensional linear representation over every field kills `𝔇_G(L)` — is
`manuscriptPrintedDefectFiniteDimensionalSterility`, stated separately because
it carries neither a countability nor a property-`(T)` hypothesis. -/
def OneSidedCompressionCriterion : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
    HasKazhdanPropertyT.{0, 0} ↥L →
      (∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
          K ≤ printedDefect L → K ≤ manuscriptCoronaMFResidual G) ∧
        (∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
          K ≤ printedDefect L → K ≠ ⊥ → ¬ IsCDEOperatorMF G) ∧
        (HasKazhdanPropertyT.{0, 0} G → printedDefect L = ⊤ →
          manuscriptCoronaMFResidual G = ⊤)

theorem manuscriptOneSidedCompressionCriterion : OneSidedCompressionCriterion := by
  intro G _ _ L hL
  have key : ∀ (K : Subgroup G) [K.Normal], HasKazhdanPropertyT.{0, 0} ↥K →
      K ≤ printedDefect L → K ≤ manuscriptCoronaMFResidual G := by
    intro K _ hK hKD
    have hres : K ≤ actualCoronaMFResidual G :=
      normalKazhdan_le_actualCoronaMFResidual_of_le_printedDefect
        L hL K hK hKD
    rwa [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  refine ⟨key, ?_, ?_⟩
  · intro K _ hK hKD hne hMF
    rw [isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot] at hMF
    exact hne (le_bot_iff.mp (hMF ▸ key K hK hKD))
  · intro hG hD
    refine top_le_iff.mp ?_
    haveI : HasKazhdanPropertyT.{0, 0} ↥(⊤ : Subgroup G) :=
      HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv hG
    exact key ⊤ this hD.ge

/-- **A full MF radical kills every homomorphism into an MF group.**  The
sentence following Theorem~A's displayed conclusion, and the last clause of
`thm:headline`. -/
def FullRadicalKillsMFTargets : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (M : Type) [Group M] [Countable M],
    manuscriptCoronaMFResidual G = ⊤ → IsCDEOperatorMF M →
      ∀ (f : G →* M) (x : G), f x = 1

theorem manuscriptFullRadicalKillsMFTargets : FullRadicalKillsMFTargets := by
  intro G _ _ M _ _ hG hM f x
  have hMbot : manuscriptCoronaMFResidual M = ⊥ :=
    (isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot).mp hM
  have hmem : f x ∈ (manuscriptCoronaMFResidual G).map f :=
    Subgroup.mem_map_of_mem _ (by rw [hG]; exact Subgroup.mem_top x)
  have := map_manuscriptCoronaMFResidual_le f hmem
  rw [hMbot] at this
  simpa using this

end OneSidedMFRadical
end Manuscript
end GroupApproximation
