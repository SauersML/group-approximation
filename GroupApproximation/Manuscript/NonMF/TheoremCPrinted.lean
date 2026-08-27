import GroupApproximation.Manuscript.NonMF.TorsionFreeTheoremC
import GroupApproximation.Sofic.ChiodoBelegradekTheorem

/-!
# Theorem C (`thm:torsion-free`), in the simplified printed statement

> **Theorem C.**  There is a two-generated, finitely presented, torsion-free,
> acylindrically hyperbolic group `Q` with property (T) such that every
> homomorphism from `Q` to an MF group is trivial.  In particular, no
> nontrivial quotient of `Q` is MF.

`TorsionFreeTheoremC.manuscriptTorsionFreeFullMFRadical` proves the radical
form (`Rad_MF(Q) = Q`, and the same for every nontrivial quotient) from the
paragraph's cited inputs.  This module restates the conclusion as printed and
proves the two closing steps of the printed proof as their own declarations:
a subgroup of an MF group is MF (`IsCDEOperatorMF.of_injective`), and the
identity map is a homomorphism to an MF group, so a nontrivial group all of
whose homomorphisms to MF groups are trivial is not MF
(`not_isCDEOperatorMF_of_killsMFTargets`).
-/

namespace GroupApproximation

/-- **A subgroup of an MF group is MF**: restrict the corona embedding. -/
theorem IsCDEOperatorMF.of_injective {H M : Type} [Group H] [Countable H]
    [Group M] [Countable M] (hM : IsCDEOperatorMF M) (f : H →* M)
    (hf : Function.Injective f) : IsCDEOperatorMF H := by
  obtain ⟨d, hd, hmono, rho, hrho⟩ := hM
  exact ⟨d, hd, hmono, rho.comp f, hrho.comp hf⟩

namespace Manuscript
namespace NonMF
namespace TheoremC

/-- "Every homomorphism from `Q` to an MF group is trivial." -/
def KillsAllMFTargets (Q : Type) [Group Q] : Prop :=
  ∀ (M : Type) (_ : Group M) (_ : Countable M), IsCDEOperatorMF M →
    ∀ (f : Q →* M) (x : Q), f x = 1

/-- **The identity map is a homomorphism to an MF group**: a nontrivial group
every one of whose homomorphisms to MF groups is trivial is not MF. -/
theorem not_isCDEOperatorMF_of_killsMFTargets {Q : Type} [Group Q] [Countable Q]
    [Nontrivial Q] (h : KillsAllMFTargets Q) : ¬ IsCDEOperatorMF Q := by
  intro hQ
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  exact hx (h Q inferInstance inferInstance hQ (MonoidHom.id Q) x)

/-- **"In particular, no nontrivial quotient of `Q` is MF"**: a homomorphism
onto an MF quotient would be a nontrivial homomorphism to an MF group. -/
theorem quotient_not_isCDEOperatorMF_of_killsMFTargets {Q : Type} [Group Q]
    (h : KillsAllMFTargets Q) {L : Type} [Group L] [Countable L] (r : Q →* L)
    (hr : Function.Surjective r) [Nontrivial L] : ¬ IsCDEOperatorMF L := by
  intro hL
  obtain ⟨y, hy⟩ := exists_ne (1 : L)
  obtain ⟨x, rfl⟩ := hr y
  exact hy (h L inferInstance inferInstance hL r x)

/-- **Theorem C, in the simplified printed statement.** -/
def PrintedTorsionFreeSimplified : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      TorsionFree.IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
      KillsAllMFTargets Q ∧
      (∀ (L : Type) (_ : Group L) (_ : Countable L) (r : Q →* L),
        Function.Surjective r → Nontrivial L → ¬ IsCDEOperatorMF L)

/-- **Theorem C, proved along the printed proof, from the paragraph's cited
inputs**, in the simplified statement: the radical form
`manuscriptTorsionFreeFullMFRadical` followed by the two closing steps. -/
theorem manuscriptTorsionFreeSimplified (I : LiteratureInputs)
    (hHull : TorsionFree.HullInputs.{0}) : PrintedTorsionFreeSimplified := by
  obtain ⟨Q, instQ, h2, hfp, htf, hah, hT, hrad, _, _⟩ :=
    manuscriptTorsionFreeFullMFRadical I hHull
  letI := instQ
  haveI : Group.IsFinitelyPresented Q := hfp
  haveI : Countable Q := ChiodoBelegradek.countable_of_isFinitelyPresented Q
  have hkills : KillsAllMFTargets Q := by
    intro M instM instC hM f x
    letI := instM
    letI := instC
    exact OneSidedMFRadical.manuscriptFullRadicalKillsMFTargets Q M hrad hM f x
  refine ⟨Q, instQ, h2, hfp, htf, hah, hT, hkills, ?_⟩
  intro L instL instC r hr hL
  letI := instL
  letI := instC
  haveI := hL
  exact quotient_not_isCDEOperatorMF_of_killsMFTargets hkills r hr

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
