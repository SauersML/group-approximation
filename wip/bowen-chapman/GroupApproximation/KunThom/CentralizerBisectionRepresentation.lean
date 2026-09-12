import GroupApproximation.KunThom.CentralizerBisectionRepresentationDefects
import GroupApproximation.KunThom.FixedPointNormalizationScaledBisection
import GroupApproximation.KunThom.FixedPointNormalizationSummation
import GroupApproximation.KunThom.CountingEndgameCompletion

/-!
# The bisection representing an almost-centralizer

The forward half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4): a permutation
`q` of the ambient model is represented by a patched total bisection of the
cluster groupoid.  On an object `X` the natural arrow is the bridge realized by
`q` from `X` into the block it carries `X` to.

* `BlockEmbedding.IsSelectedBlock` and `selectedTarget`: a block is selected
  when its bridge into some block is a cluster candidate at the scale of the
  pair.  That block is unique, and `selectedTarget_injOn` shows that distinct
  selected blocks have distinct targets.
* For a `ScaledPartialClusterSystem` placed in the ambient model:
  `selectedObjects`, `selectedObjectTarget` and `selectedArrow` form the partial
  bisection carried by `q`, and `exists_bisection_selected` completes it inside
  the orbits (`CountingEndgame.exists_bisection_extend`).
* `hom_eq_ofRep_bridge`, `scaledBisectionRep_near_bridge` and
  `near_bridge_of_selected`: at every selected object the arrow of the completed
  bisection is the class of the bridge, so its chosen representative lies within
  the pair radius of the bridge.
* `card_hammingDisagreement_scaledBisectionPatch_le`: the patched bisection
  differs from `q` by at most the mass off its glued domain, the re-separation
  scales of the retained objects and the full size of the other objects.  The
  bridges realize `q` exactly, so they serve as the reference arrows of
  `BlockArrows.card_hammingDisagreement_patch_le_reseparation`.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection CategoryTheory

universe u

variable {Y : FiniteModel} {I : Type u}

namespace BlockEmbedding

/-- **A block receives at most one candidate bridge**, with separate scales for the two
bridges. -/
theorem eq_of_isClusterCandidate_bridge_target_of_scales {L : Type*} [Fintype L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) {C C' D : I}
    (actC : L → Equiv.Perm (E.model C)) (actC' : L → Equiv.Perm (E.model C'))
    (actD : L → Equiv.Perm (E.model D)) {h : ℝ} {m m' : ℕ}
    (hsize : 17 * m ≤ Fintype.card (E.model D))
    (hsize' : 17 * m' ≤ Fintype.card (E.model D))
    (hC : (E.bridge q C D).IsClusterCandidate actC actD h m)
    (hC' : (E.bridge q C' D).IsClusterCandidate actC' actD h m') : C = C' := by
  by_contra hne
  have hcard := card_le_targetDefect_add_of_disjoint (E.bridge q C D) (E.bridge q C' D)
    (E.disjoint_bridge_target q D hne)
  have h₁ := hC.selfSmall
  have h₂ := hC'.selfSmall
  omega

/-! ### Selected blocks -/

/-- A block is selected when its bridge into some block is a cluster candidate at the scale
of the pair. -/
def IsSelectedBlock {L : Type*} [Fintype L] (E : BlockEmbedding Y I)
    (act : ∀ C, L → Equiv.Perm (E.model C)) (h : ℝ) (m : I → I → ℕ) (q : Equiv.Perm Y)
    (C : I) : Prop :=
  ∃ D, (E.bridge q C D).IsClusterCandidate (act C) (act D) h (m C D)

/-- The target block of a selected block, and the block itself otherwise. -/
noncomputable def selectedTarget {L : Type*} [Fintype L] (E : BlockEmbedding Y I)
    (act : ∀ C, L → Equiv.Perm (E.model C)) (h : ℝ) (m : I → I → ℕ) (q : Equiv.Perm Y)
    (C : I) : I := by
  classical
  exact if hC : E.IsSelectedBlock act h m q C then Classical.choose hC else C

theorem selectedTarget_spec {L : Type*} [Fintype L] (E : BlockEmbedding Y I)
    (act : ∀ C, L → Equiv.Perm (E.model C)) (h : ℝ) (m : I → I → ℕ) (q : Equiv.Perm Y)
    {C : I} (hC : E.IsSelectedBlock act h m q C) :
    (E.bridge q C (E.selectedTarget act h m q C)).IsClusterCandidate (act C)
      (act (E.selectedTarget act h m q C)) h (m C (E.selectedTarget act h m q C)) := by
  have hT : E.selectedTarget act h m q C = Classical.choose hC := by
    rw [selectedTarget, dif_pos hC]
  rw [hT]
  exact Classical.choose_spec hC

/-- **Distinct selected blocks have distinct targets.** -/
theorem selectedTarget_injOn {L : Type*} [Fintype L] (E : BlockEmbedding Y I)
    (act : ∀ C, L → Equiv.Perm (E.model C)) (h : ℝ) (m : I → I → ℕ) (q : Equiv.Perm Y)
    (hsize : ∀ C D, 17 * m C D ≤ Fintype.card (E.model D)) {C C' : I}
    (hC : E.IsSelectedBlock act h m q C) (hC' : E.IsSelectedBlock act h m q C')
    (heq : E.selectedTarget act h m q C = E.selectedTarget act h m q C') : C = C' := by
  have h₁ := E.selectedTarget_spec act h m q hC
  have h₂ := E.selectedTarget_spec act h m q hC'
  rw [← heq] at h₂
  exact E.eq_of_isClusterCandidate_bridge_target_of_scales q (act C) (act C')
    (act (E.selectedTarget act h m q C)) (hsize C _) (hsize C' _) h₁ h₂

end BlockEmbedding

/-! ### The partial bisection carried by an almost-centralizer -/

/-- The objects of a scaled cluster system whose bridge under `q` into some object is a
cluster candidate at the pair scale. -/
noncomputable def selectedObjects [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) : Finset D.presentation.Obj := by
  classical
  exact Finset.univ.filter fun X ↦
    (scaledClusterEmbedding D.clusterData ι hinj hdisj).IsSelectedBlock D.act D.h
      (fun X X' ↦ min (D.scale X) (D.scale X')) q X.val

theorem mem_selectedObjects [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) (X : D.presentation.Obj) :
    X ∈ selectedObjects D ι hinj hdisj q ↔
      (scaledClusterEmbedding D.clusterData ι hinj hdisj).IsSelectedBlock D.act D.h
        (fun X X' ↦ min (D.scale X) (D.scale X')) q X.val := by
  classical
  simp [selectedObjects]

/-- The selected target of an object. -/
noncomputable def selectedObjectTarget [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) (X : D.presentation.Obj) : D.presentation.Obj :=
  ⟨(scaledClusterEmbedding D.clusterData ι hinj hdisj).selectedTarget D.act D.h
    (fun X X' ↦ min (D.scale X) (D.scale X')) q X.val⟩

/-- **The selected object map is injective on the selected objects.** -/
theorem selectedObjectTarget_injOn [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) :
    Set.InjOn (selectedObjectTarget D ι hinj hdisj q)
      (selectedObjects D ι hinj hdisj q : Set D.presentation.Obj) := by
  intro X hX X' hX' heq
  have hsel := (mem_selectedObjects D ι hinj hdisj q X).mp (Finset.mem_coe.mp hX)
  have hsel' := (mem_selectedObjects D ι hinj hdisj q X').mp (Finset.mem_coe.mp hX')
  have hval : X.val = X'.val :=
    (scaledClusterEmbedding D.clusterData ι hinj hdisj).selectedTarget_injOn D.act D.h
      (fun X X' ↦ min (D.scale X) (D.scale X')) q (fun X X' ↦ D.size_min_right X X')
      hsel hsel' (congrArg GroupoidPresentation.Obj.val heq)
  cases X
  cases X'
  exact congrArg GroupoidPresentation.Obj.mk hval

/-- The class of the bridge at a selected object, an arrow of the cluster groupoid into the
selected target. -/
noncomputable def selectedArrow [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) (X : D.presentation.Obj)
    (hX : X ∈ selectedObjects D ι hinj hdisj q) :
    X ⟶ selectedObjectTarget D ι hinj hdisj q X :=
  D.presentation.ofRep
    ⟨(scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X.val
        ((scaledClusterEmbedding D.clusterData ι hinj hdisj).selectedTarget D.act D.h
          (fun X X' ↦ min (D.scale X) (D.scale X')) q X.val),
      (FinitePartialBijection.mem_clusterCandidates _ _ _ _ _).mpr
        ((scaledClusterEmbedding D.clusterData ι hinj hdisj).selectedTarget_spec D.act D.h
          (fun X X' ↦ min (D.scale X) (D.scale X')) q
          ((mem_selectedObjects D ι hinj hdisj q X).mp hX))⟩

/-- **Completion.**  Some total bisection of the cluster groupoid has, at every selected
object, the selected arrow, up to the identification of its target. -/
theorem exists_bisection_selected [Fintype I] [DecidableEq I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L)
    (ι : ∀ X, D.model X → Y) (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) :
    ∃ b : FiniteGroupoid.Bisection D.presentation.Obj,
      ∀ X (hX : X ∈ selectedObjects D ι hinj hdisj q),
        ∃ e : b.objEquiv X = selectedObjectTarget D ι hinj hdisj q X,
          b.hom X ≫ eqToHom e = selectedArrow D ι hinj hdisj q X hX :=
  CountingEndgame.exists_bisection_extend (selectedObjects D ι hinj hdisj q)
    (selectedObjectTarget D ι hinj hdisj q) (selectedObjectTarget_injOn D ι hinj hdisj q)
    (selectedArrow D ι hinj hdisj q)

/-- **A completed bisection keeps the bridge.**  If an arrow `f` out of a selected object,
followed by an identification of its target with the selected target, is the selected
arrow, then `f` is the class of the bridge into its own target. -/
theorem hom_eq_ofRep_bridge [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) {X W : D.presentation.Obj}
    (hX : X ∈ selectedObjects D ι hinj hdisj q) (f : X ⟶ W)
    (e : W = selectedObjectTarget D ι hinj hdisj q X)
    (hf : f ≫ eqToHom e = selectedArrow D ι hinj hdisj q X hX) :
    ∃ hc : ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X.val
        W.val).IsClusterCandidate (D.act X.val) (D.act W.val) D.h
          (min (D.scale X.val) (D.scale W.val)),
      f = D.presentation.ofRep
        ⟨(scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X.val W.val,
          (FinitePartialBijection.mem_clusterCandidates _ _ _ _ _).mpr hc⟩ := by
  subst e
  refine ⟨(scaledClusterEmbedding D.clusterData ι hinj hdisj).selectedTarget_spec D.act D.h
    (fun X X' ↦ min (D.scale X) (D.scale X')) q
    ((mem_selectedObjects D ι hinj hdisj q X).mp hX), ?_⟩
  rw [eqToHom_refl, Category.comp_id] at hf
  exact hf

/-- **The representative of a bridge class is near the bridge.** -/
theorem scaledBisectionRep_near_bridge [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) (b : FiniteGroupoid.Bisection D.presentation.Obj) (X : I)
    (hc : ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
      (scaledBisectionIndexEquiv (D := D.clusterData) b X)).IsClusterCandidate (D.act X)
        (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X)) D.h
        (min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X))))
    (hb : b.hom ⟨X⟩ = D.presentation.ofRep
      ⟨(scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X),
        (FinitePartialBijection.mem_clusterCandidates _ _ _ _ _).mpr hc⟩) :
    (scaledBisectionRep (D := D.clusterData) b X).1.twoSidedDisagreement
        ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
          (scaledBisectionIndexEquiv (D := D.clusterData) b X)) <
      2 * min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X)) := by
  have hrel : D.clusterData.Near (scaledBisectionRep (D := D.clusterData) b X)
      ⟨(scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
        (scaledBisectionIndexEquiv (D := D.clusterData) b X),
        (FinitePartialBijection.mem_clusterCandidates _ _ _ _ _).mpr hc⟩ := by
    rw [scaledBisectionRep, hb]
    exact Quotient.mk_out _
  exact hrel

/-- **At a selected object, the arrow of a completed bisection is near the bridge.** -/
theorem near_bridge_of_selected [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (hb : ∀ X (hX : X ∈ selectedObjects D ι hinj hdisj q),
      ∃ e : b.objEquiv X = selectedObjectTarget D ι hinj hdisj q X,
        b.hom X ≫ eqToHom e = selectedArrow D ι hinj hdisj q X hX)
    {X : I} (hX : (⟨X⟩ : D.presentation.Obj) ∈ selectedObjects D ι hinj hdisj q) :
    ((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X).twoSidedDisagreement
        ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
          (scaledBisectionIndexEquiv (D := D.clusterData) b X)) <
      2 * min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X)) := by
  obtain ⟨e, he⟩ := hb ⟨X⟩ hX
  obtain ⟨hc, hf⟩ := hom_eq_ofRep_bridge D ι hinj hdisj q hX (b.hom ⟨X⟩) e he
  exact scaledBisectionRep_near_bridge D ι hinj hdisj q b X hc hf

/-- At a selected object, a completed bisection moves the object to its selected target. -/
theorem scaledBisectionIndexEquiv_eq_selectedTarget [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L)
    (ι : ∀ X, D.model X → Y) (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) (b : FiniteGroupoid.Bisection D.presentation.Obj)
    (hb : ∀ X (hX : X ∈ selectedObjects D ι hinj hdisj q),
      ∃ e : b.objEquiv X = selectedObjectTarget D ι hinj hdisj q X,
        b.hom X ≫ eqToHom e = selectedArrow D ι hinj hdisj q X hX)
    {X : I} (hX : (⟨X⟩ : D.presentation.Obj) ∈ selectedObjects D ι hinj hdisj q) :
    scaledBisectionIndexEquiv (D := D.clusterData) b X =
      (scaledClusterEmbedding D.clusterData ι hinj hdisj).selectedTarget D.act D.h
        (fun X X' ↦ min (D.scale X) (D.scale X')) q X := by
  obtain ⟨e, _⟩ := hb ⟨X⟩ hX
  exact congrArg GroupoidPresentation.Obj.val e

/-! ### The patched bisection against `q` -/

/-- **The patched bisection against `q`.**  The bridges realize `q` exactly, so on the
retained objects they serve as reference arrows.  The patched bisection differs from `q` by
at most the mass off its glued domain, the re-separation scales `x X` of the retained
objects, and the full size of the other objects. -/
theorem card_hammingDisagreement_scaledBisectionPatch_le [Fintype I] [DecidableEq I]
    {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')
    (q : Equiv.Perm Y) (b : FiniteGroupoid.Bisection D.presentation.Obj) (good : Finset I)
    {c : ℝ} (hexp : ∀ X, HasTaggedExpansionAtScale (D.act X) c 1) (x : I → ℝ)
    (hx : ∀ X ∈ good, 0 ≤ x X)
    (hdefect : ∀ X ∈ good,
      (((((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X).equivarianceDefect
          (D.act X) (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card +
        (((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
          (scaledBisectionIndexEquiv (D := D.clusterData) b X)).equivarianceDefect (D.act X)
            (D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X))).card : ℕ) : ℝ) <
        c * ((⌊x X⌋₊ + 1 : ℕ) : ℝ))
    (hnear : ∀ X ∈ good,
      ((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X).twoSidedDisagreement
        ((scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
          (scaledBisectionIndexEquiv (D := D.clusterData) b X)) <
        2 * min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X)))
    (hroom : ∀ X ∈ good,
      2 * min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X)) +
        (⌊x X⌋₊ + 1) ≤ Fintype.card (D.model X)) :
    ((hammingDisagreement (scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).patch
      q).card : ℝ) ≤
      ((Finset.univ \ (scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).domain).card :
        ℝ) + ∑ X ∈ good, x X + ∑ X ∈ goodᶜ, (Fintype.card (D.model X) : ℝ) :=
  (scaledBisectionArrows (D := D.clusterData) ι hinj hdisj
    b).card_hammingDisagreement_patch_le_reseparation q good
    (fun X ↦ (scaledClusterEmbedding D.clusterData ι hinj hdisj).bridge q X
      (scaledBisectionIndexEquiv (D := D.clusterData) b X))
    (fun X _ ↦ BlockEmbedding.realizesOn_bridge _ q X) D.act
    (fun X ↦ D.act (scaledBisectionIndexEquiv (D := D.clusterData) b X)) c x
    (fun X ↦ min (D.scale X) (D.scale (scaledBisectionIndexEquiv (D := D.clusterData) b X)))
    hx (fun X _ ↦ hasTaggedExpansionAtScale_mono (hexp X) (by omega)) hdefect
    (fun X hX ↦ (Nat.le_add_right _ _).trans_lt (hnear X hX)) hroom

end BlockPatching
end GroupApproximation
