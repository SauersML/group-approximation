import GroupApproximation.Sofic.InvolutionCollapseEndpoint
import GroupApproximation.Algebra.CountableInstances

/-!
# Defect saturation: full MF radicals from saturated collapse defects

**Credit.**  The saturation principle formalized here — *detect a defect
analytically, then saturate it algebraically so the radical becomes the
whole group* — develops a suggestion of Francesco Fournier-Facio
(personal communication, 2026-08-14), who proposed that the affine
globalization argument can be replaced by a small cancellation argument
"analogously to" his construction in arXiv:2608.02025; the surrounding
full-radical/black-hole framing was elaborated from that suggestion on
the user's side (GPT-5.6-assisted).  The collapse theorem itself
(`InvolutionCollapseEndpoint`) is independent of this suggestion and is
not part of the credited material.  The *existence* of saturating
small-cancellation quotients (Hull/Osin acylindrical machinery) is not
formalized and nothing below assumes it: every theorem in this file is
an exact, unconditional implication.

Contents: if the involutive collapse defect of a Kazhdan subgroup with a
one-sided compressor saturates (`= ⊤`), then the literal MF radical is
the whole group, every element is invisible in every corona
representation, every homomorphism to a countable operator-MF group is
trivial (the *approximation black hole*), and the group itself is not
operator-MF once nontrivial.  Without saturation, the defect still
absorbs into the kernel of every map to an operator-MF group.
-/

namespace GroupApproximation
namespace DefectSaturation

open InvolutionCollapseEndpoint
open scoped commutatorElement

variable {E : Type} [Group E]

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-- **Unconditional MF-kernel absorption.**  Even without saturation,
the involutive collapse defect dies in every homomorphism to a countable
operator-MF group. -/
theorem involutiveCollapseDefect_le_ker_of_isCDEOperatorMF [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    {Q : Type} [Group Q] [Countable Q]
    (f : E →* Q) (hQ : IsCDEOperatorMF Q) :
    involutiveCollapseDefect L s ≤ f.ker := by
  refine le_trans
    (involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp) ?_
  intro x hx
  have hfx : f x ∈ actualCoronaMFResidual Q :=
    map_actualCoronaMFResidual_le f ⟨x, hx, rfl⟩
  have hbot : actualCoronaMFResidual Q = ⊥ :=
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hQ
  rw [hbot] at hfx
  exact Subgroup.mem_bot.mp hfx

/-- **Saturation gives the full MF radical** (after Fournier-Facio's
saturation suggestion): if the involutive collapse defect is the whole
group, the literal MF radical is the whole group. -/
theorem actualCoronaMFResidual_eq_top_of_saturated [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hsat : involutiveCollapseDefect L s = ⊤) :
    actualCoronaMFResidual E = ⊤ := by
  refine top_unique ?_
  rw [← hsat]
  exact involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp

/-- With a saturated defect, every element is invisible in every norm
matrix C*-corona representation. -/
theorem actualCoronaMFInvisible_of_saturated [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hsat : involutiveCollapseDefect L s = ⊤) (x : E) :
    ActualCoronaMFInvisible x := by
  have h := actualCoronaMFResidual_eq_top_of_saturated hkazhdan hcomp hsat
  have hx : x ∈ actualCoronaMFResidual E := by
    rw [h]
    trivial
  exact hx

/-- **The approximation black hole**: with a saturated defect, every
homomorphism to a countable operator-MF group is trivial. -/
theorem map_eq_one_of_saturated [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hsat : involutiveCollapseDefect L s = ⊤)
    {Q : Type} [Group Q] [Countable Q]
    (f : E →* Q) (hQ : IsCDEOperatorMF Q) (x : E) : f x = 1 := by
  have hker := involutiveCollapseDefect_le_ker_of_isCDEOperatorMF
    hkazhdan hcomp f hQ
  have hx : x ∈ involutiveCollapseDefect L s := by
    rw [hsat]
    trivial
  exact hker hx

/-- A nontrivial group with a saturated involutive collapse defect is
not operator-MF. -/
theorem not_isCDEOperatorMF_of_saturated [Countable E] [Nontrivial E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hsat : involutiveCollapseDefect L s = ⊤) :
    ¬ IsCDEOperatorMF E := by
  intro hMF
  have hbot : actualCoronaMFResidual E = ⊥ :=
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hMF
  have htop := actualCoronaMFResidual_eq_top_of_saturated hkazhdan hcomp
    hsat
  rw [htop] at hbot
  obtain ⟨x, y, hxy⟩ := exists_pair_ne E
  apply hxy
  have hx : x * y⁻¹ ∈ (⊤ : Subgroup E) := trivial
  rw [hbot] at hx
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hx)

end DefectSaturation
end GroupApproximation
