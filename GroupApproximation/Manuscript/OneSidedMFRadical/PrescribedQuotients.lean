import GroupApproximation.Sofic.MFCamouflageRadical
import GroupApproximation.Algebra.CountableInstances

/-!
# Prescribed MF quotients

This module holds the exact manuscript-facing endpoints for
`non_mf_groups_exist.tex`, Section `sec:prescribed-quotients`:

* `SplitPrescribedProjection` — the unnumbered opening paragraph: the
  amalgam `W_Q = B *_A (Q × A)` with `A = ⟨d⟩`, the epimorphism
  `π_Q : W_Q → Q`, its splitting `Q → Q × A → W_Q`, injectivity of both
  vertex maps, and the consequence `d ≠ 1` in `W_Q`.
* `PrescribedMFQuotients` — Theorem `thm:prescribed-quotients`.
* `PrescribedQuotientRelationCalculus` — the closing display
  `eq:closure-pullback` together with the MF criterion for `W_Q / N` and the
  preimage identity `N = π_Q⁻¹(π_Q(N))` that it relies on.

Injectivity of the vertex maps is *not* assumed here: the normal-form input
the manuscript invokes is discharged inside the development by
`Higman.Amalgam.of_injective_push`, which is `Monoid.PushoutI.of_injective`.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-- **The split projection of `sec:prescribed-quotients`.** For the amalgam
`W_Q = B *_A (Q × A)` with `A = ⟨d⟩`, the two vertex maps to `Q` — trivial
on `B`, the projection on `Q × A` — agree on the edge group, so they
define `π_Q : W_Q → Q`. It is onto, split by the manuscript's inclusion
`Q → Q × A → W_Q`, and both vertex maps of the amalgam are injective; in
particular `d ≠ 1` in `W_Q`. The edge group is cyclic, as `A = ⟨d⟩`
requires. -/
def SplitPrescribedProjection : Prop :=
  ∀ (B Q : Type) [Group B] [Group Q] (d : B),
    IsCyclic ↥(MFCamouflage.Edge d) ∧
      (∀ b : B,
        MFCamouflage.projection d Q (MFCamouflage.blackHole d Q b) = 1) ∧
      (∀ x : Q × ↥(MFCamouflage.Edge d), MFCamouflage.projection d Q
          (MFCamouflage.productVertex d Q x) = x.1) ∧
      MFCamouflage.visible d Q =
        (MFCamouflage.productVertex d Q).comp
          (MonoidHom.inl Q ↥(MFCamouflage.Edge d)) ∧
      Function.Surjective (MFCamouflage.projection d Q) ∧
      (MFCamouflage.projection d Q).comp (MFCamouflage.visible d Q) =
        MonoidHom.id Q ∧
      Function.Injective (MFCamouflage.blackHole d Q) ∧
      Function.Injective (MFCamouflage.productVertex d Q) ∧
      (d ≠ 1 → MFCamouflage.defect d Q ≠ 1)

/-- Closed proof of the opening paragraph of `sec:prescribed-quotients`. -/
theorem manuscriptSplitPrescribedProjection : SplitPrescribedProjection := by
  intro B Q _ _ d
  exact ⟨MFCamouflage.edgeIsCyclic d,
    MFCamouflage.projection_blackHole d Q,
    MFCamouflage.projection_productVertex d Q,
    rfl,
    MFCamouflage.projection_surjective d Q,
    MFCamouflage.projection_comp_visible d Q,
    MFCamouflage.blackHole_injective d Q,
    MFCamouflage.productVertex_injective d Q,
    MFCamouflage.defect_ne_one d Q⟩

/-- **Theorem `thm:prescribed-quotients`.** A countable full-MF-radical group
with a nontrivial normal generator can be hidden behind any prescribed
countable quotient. The split projection transplants the MF radical, its
source is non-MF, and it is universal for maps to MF groups. -/
def PrescribedMFQuotients : Prop :=
  ∀ (B Q : Type) [Group B] [Group Q] [Countable B] [Countable Q]
    (d : B),
    actualCoronaMFResidual B = ⊤ → d ≠ 1 →
    Subgroup.normalClosure ({d} : Set B) = ⊤ →
      (Function.Surjective (MFCamouflage.projection d Q) ∧
        (MFCamouflage.projection d Q).comp (MFCamouflage.visible d Q) =
          MonoidHom.id Q) ∧
      actualCoronaMFResidual (MFCamouflage.Camouflage d Q) =
        (actualCoronaMFResidual Q).comap (MFCamouflage.projection d Q) ∧
      ¬ IsCDEOperatorMF (MFCamouflage.Camouflage d Q) ∧
      (IsCDEOperatorMF Q →
        actualCoronaMFResidual (MFCamouflage.Camouflage d Q) =
            (MFCamouflage.projection d Q).ker ∧
          (MFCamouflage.projection d Q).ker =
            Subgroup.normalClosure
              ({MFCamouflage.defect d Q} :
                Set (MFCamouflage.Camouflage d Q))) ∧
      ∀ (M : Type) [Group M] [Countable M], IsCDEOperatorMF M →
        Function.Bijective
          (fun f : Q →* M ↦ f.comp (MFCamouflage.projection d Q))

/-- Closed proof of the prescribed-MF-quotient theorem. -/
theorem manuscriptPrescribedMFQuotients : PrescribedMFQuotients := by
  intro B Q _ _ _ _ d hfull hd hnormal
  refine ⟨⟨MFCamouflage.projection_surjective d Q,
      MFCamouflage.projection_comp_visible d Q⟩,
    MFCamouflage.actualCoronaMFResidual_eq_comap d Q hfull, ?_, ?_, ?_⟩
  · intro hMF
    have hbot :
        actualCoronaMFResidual (MFCamouflage.Camouflage d Q) = ⊥ :=
      isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hMF
    have hdefect : MFCamouflage.defect d Q ∈
        actualCoronaMFResidual (MFCamouflage.Camouflage d Q) :=
      MFCamouflage.projection_ker_le_actualCoronaMFResidual d Q hfull
        (MonoidHom.mem_ker.mpr (MFCamouflage.projection_blackHole d Q d))
    rw [hbot] at hdefect
    exact MFCamouflage.defect_ne_one d Q hd (Subgroup.mem_bot.mp hdefect)
  · intro hQ
    exact ⟨MFCamouflage.actualCoronaMFResidual_eq_ker d Q hfull hQ,
      MFCamouflage.projection_ker_eq_normalClosure d Q hnormal⟩
  · intro M _ _ hM
    exact MFCamouflage.cdeMF_precomp_bijective d Q hfull hM

/-- **The closing display `eq:closure-pullback` and its consequence.** For
every normal relation subgroup `N` of `W_Q`, the MF closure of `N` is the
`π_Q`-preimage of the MF closure of `π_Q(N)`; consequently `W_Q / N` is MF
exactly when `N` contains `ker π_Q` and `Q / π_Q(N)` is MF. The last clause is
the manuscript's "only additional observation": once `ker π_Q ≤ N`, the
relation subgroup is recovered as `N = π_Q⁻¹(π_Q(N))`. -/
def PrescribedQuotientRelationCalculus : Prop :=
  ∀ (B Q : Type) [Group B] [Group Q] [Countable B] [Countable Q]
    (d : B),
    actualCoronaMFResidual B = ⊤ →
      ∀ (N : Subgroup (MFCamouflage.Camouflage d Q)) [N.Normal],
        actualCoronaMFClosure N =
            (actualCoronaMFClosure
              (N.map (MFCamouflage.projection d Q))).comap
                (MFCamouflage.projection d Q) ∧
          (IsCDEOperatorMF (MFCamouflage.Camouflage d Q ⧸ N) ↔
            (MFCamouflage.projection d Q).ker ≤ N ∧
              IsCDEOperatorMF
                (Q ⧸ N.map (MFCamouflage.projection d Q))) ∧
          ((MFCamouflage.projection d Q).ker ≤ N →
            (N.map (MFCamouflage.projection d Q)).comap
              (MFCamouflage.projection d Q) = N)

/-- Closed proof of the prescribed-quotient relation calculus. -/
theorem manuscriptPrescribedQuotientRelationCalculus :
    PrescribedQuotientRelationCalculus := by
  intro B Q _ _ _ _ d hfull N _
  exact ⟨MFCamouflage.actualCoronaMFClosure_eq_comap d Q hfull N,
    MFCamouflage.quotient_isCDEOperatorMF_iff d Q hfull N,
    fun hker ↦ Subgroup.comap_map_eq_self hker⟩

end OneSidedMFRadical
end Manuscript
end GroupApproximation
