import GroupApproximation.KunThom.CentralizerToBisectionDefect
import GroupApproximation.KunThom.CentralizerToBisectionExtension
import GroupApproximation.KunThom.FixedPointNormalizationBisection

/-!
# Representing a permutation by a bisection of the cluster groupoid

Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4), forward direction: a permutation
of the ambient model is represented by a bisection of the cluster groupoid,
exactly on the objects where its block arrows are candidates.

Fix a cluster system `D` placed disjointly in a model `Y` and a permutation
`v` of `Y`.

* `clusterOverlap v X Z`: the overlap arrow of `v` from object `X` to object
  `Z` (`BlockPatching.BlockEmbedding.overlapArrow`).
* `overlapGood v`: the objects at which some overlap arrow of `v` is a
  candidate, and `overlapObject v X` its target.  The target is unique
  (`overlapObject_eq_of_isClusterCandidate`), and different good objects have
  different targets (`eq_of_clusterOverlap_isClusterCandidate_target`).
* `representingPerm v`: a permutation of the objects which agrees with
  `overlapObject v` on `overlapGood v` and keeps every object in its
  connectivity class.
* `representingArrow v X`: the overlap arrow on good objects and some
  candidate elsewhere.  Every representing arrow is a candidate.
* `representingBisection v`: the bisection with these arrows.  Its chosen
  representatives lie within `2 * scale` of the representing arrows
  (`twoSidedDisagreement_bisectionRep_lt`), and by the distance gap every
  candidate within `16 * scale` of a representing arrow represents the same
  arrow (`representingBisection_hom_eq_ofRep`).
* `card_hammingDisagreement_representingPatch_le`: the patched representing
  arrows differ from `v` only off the glued domain and on the objects outside
  `overlapGood v`.
* `card_compl_overlapGood_mul_le`: along any object map `π`, every object
  outside `overlapGood v` carries forward plus inverse defect at least
  `h * scale / 2`.  With `sum_card_equivarianceDefect_clusterOverlap_le` and
  `sum_card_symm_equivarianceDefect_clusterOverlap_le` this bounds the number
  of objects outside `overlapGood v` by commutation, compatibility and leakage
  counts.
-/

namespace GroupApproximation

universe u

namespace PartialClusterSystem

open BlockPatching FinitePartialBijection

variable {I : Type u} [Fintype I] {L : Type*} [Fintype L] [DecidableEq L]
variable (D : PartialClusterSystem I L)

/-- Two objects are connected when a candidate arrow joins them. -/
abbrev Connected (X Z : I) : Prop := Nonempty (D.clusterData.Rep X Z)

theorem connected_refl (X : I) : D.Connected X X :=
  ⟨⟨_, D.clusterData.one_mem X⟩⟩

theorem connected_symm {X Z : I} (h : D.Connected X Z) : D.Connected Z X :=
  Nonempty.elim h fun f ↦ ⟨⟨f.1.symm, D.clusterData.symm_mem f.1 f.2⟩⟩

theorem connected_trans {X Z W : I} (h₁ : D.Connected X Z) (h₂ : D.Connected Z W) :
    D.Connected X W :=
  Nonempty.elim h₁ fun f ↦ Nonempty.elim h₂ fun g ↦
    ⟨⟨D.clusterData.improve f.1 g.1, D.clusterData.improve_mem f.1 f.2 g.1 g.2⟩⟩

/-- A candidate arrow connects its endpoints. -/
theorem connected_of_isClusterCandidate {X Z : I}
    (f : FinitePartialBijection (D.model X) (D.model Z))
    (hf : f.IsClusterCandidate (D.act X) (D.act Z) D.h D.scale) : D.Connected X Z :=
  ⟨⟨f, (mem_clusterCandidates (D.act X) (D.act Z) D.h D.scale f).mpr hf⟩⟩

/-- The connectivity class of an object. -/
def connectedClass (X : I) : Set I := {Z | D.Connected X Z}

theorem connectedClass_eq_of_connected {X Z : I} (h : D.Connected X Z) :
    D.connectedClass Z = D.connectedClass X := by
  ext W
  constructor
  · intro hW
    exact D.connected_trans (W := W) h hW
  · intro hW
    exact D.connected_trans (W := W) (D.connected_symm h) hW

variable {Y : FiniteModel} (ι : ∀ X, D.model X → Y)
  (hinj : ∀ X, Function.Injective (ι X))
  (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'), ι X x = ι X' z → X = X')

/-- The overlap arrow of `v` from object `X` to object `Z`. -/
noncomputable def clusterOverlap (v : Equiv.Perm Y) (X Z : I) :
    FinitePartialBijection (D.model X) (D.model Z) :=
  (clusterEmbedding D ι hinj hdisj).overlapArrow v X Z

theorem embed_clusterOverlap_apply (v : Equiv.Perm Y) (X Z : I) (x : D.model X)
    (hx : x ∈ (D.clusterOverlap ι hinj hdisj v X Z).source) :
    ι Z ((D.clusterOverlap ι hinj hdisj v X Z).apply x hx) = v (ι X x) :=
  (clusterEmbedding D ι hinj hdisj).embed_overlapArrow_apply v X Z x hx

/-- **Unique target.**  Candidate overlap arrows out of one object have the
same target. -/
theorem overlapObject_unique (v : Equiv.Perm Y) {X Z Z' : I}
    (hZ : (D.clusterOverlap ι hinj hdisj v X Z).IsClusterCandidate (D.act X) (D.act Z)
      D.h D.scale)
    (hZ' : (D.clusterOverlap ι hinj hdisj v X Z').IsClusterCandidate (D.act X)
      (D.act Z') D.h D.scale) : Z = Z' :=
  (clusterEmbedding D ι hinj hdisj).eq_of_overlapArrow_sourceDefect_lt v (C := X)
    (m := D.scale) (lt_of_le_of_lt (Nat.le_add_right _ _) hZ.selfSmall)
    (lt_of_le_of_lt (Nat.le_add_right _ _) hZ'.selfSmall)
    (le_trans (by omega) (D.size X))

/-- **Injective on objects.**  Candidate overlap arrows into one object have
the same source. -/
theorem eq_of_clusterOverlap_isClusterCandidate_target (v : Equiv.Perm Y)
    {X X' Z : I}
    (hX : (D.clusterOverlap ι hinj hdisj v X Z).IsClusterCandidate (D.act X) (D.act Z)
      D.h D.scale)
    (hX' : (D.clusterOverlap ι hinj hdisj v X' Z).IsClusterCandidate (D.act X')
      (D.act Z) D.h D.scale) : X = X' :=
  (clusterEmbedding D ι hinj hdisj).eq_of_overlapArrow_targetDefect_lt v (C := Z)
    (m := D.scale) (lt_of_le_of_lt (Nat.le_add_left _ _) hX.selfSmall)
    (lt_of_le_of_lt (Nat.le_add_left _ _) hX'.selfSmall)
    (le_trans (by omega) (D.size Z))

/-- **An object permutation.**  If on `good` the overlap arrow of `v` into `π X`
is a candidate, some permutation of the objects agrees with `π` on `good` and
keeps every object in its connectivity class. -/
theorem exists_perm_of_isClusterCandidate (v : Equiv.Perm Y) (good : Finset I)
    (π : I → I)
    (hgood : ∀ X ∈ good, (D.clusterOverlap ι hinj hdisj v X (π X)).IsClusterCandidate
      (D.act X) (D.act (π X)) D.h D.scale) :
    ∃ σ : Equiv.Perm I, (∀ X ∈ good, σ X = π X) ∧ ∀ X, D.Connected X (σ X) := by
  have hinjπ : Set.InjOn π (good : Set I) := by
    intro X hX X' hX' hπ
    have h' := hgood X' hX'
    rw [← hπ] at h'
    exact D.eq_of_clusterOverlap_isClusterCandidate_target ι hinj hdisj v
      (hgood X hX) h'
  obtain ⟨σ, hσπ, hσq⟩ := exists_perm_extending_fiberwise D.connectedClass
    (good : Set I) π hinjπ fun X hX ↦ D.connectedClass_eq_of_connected
      (D.connected_of_isClusterCandidate _ (hgood X hX))
  refine ⟨σ, hσπ, fun X ↦ ?_⟩
  have hmem : σ X ∈ D.connectedClass (σ X) := D.connected_refl (σ X)
  rw [hσq X] at hmem
  exact hmem

/-- Objects at which some overlap arrow of `v` is a candidate. -/
noncomputable def overlapGood (v : Equiv.Perm Y) : Finset I := by
  classical
  exact Finset.univ.filter fun X ↦ ∃ Z,
    (D.clusterOverlap ι hinj hdisj v X Z).IsClusterCandidate (D.act X) (D.act Z)
      D.h D.scale

theorem mem_overlapGood {v : Equiv.Perm Y} {X : I} :
    X ∈ D.overlapGood ι hinj hdisj v ↔ ∃ Z,
      (D.clusterOverlap ι hinj hdisj v X Z).IsClusterCandidate (D.act X) (D.act Z)
        D.h D.scale := by
  classical
  simp only [overlapGood, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The target of a candidate overlap arrow of `v` out of `X`, and `X` itself
when there is none. -/
noncomputable def overlapObject (v : Equiv.Perm Y) (X : I) : I := by
  classical
  exact if h : ∃ Z, (D.clusterOverlap ι hinj hdisj v X Z).IsClusterCandidate
      (D.act X) (D.act Z) D.h D.scale then Classical.choose h else X

theorem overlapObject_isClusterCandidate {v : Equiv.Perm Y} {X : I}
    (hX : X ∈ D.overlapGood ι hinj hdisj v) :
    (D.clusterOverlap ι hinj hdisj v X (D.overlapObject ι hinj hdisj v X)
      ).IsClusterCandidate (D.act X) (D.act (D.overlapObject ι hinj hdisj v X))
        D.h D.scale := by
  have h := (D.mem_overlapGood ι hinj hdisj).mp hX
  have heq : D.overlapObject ι hinj hdisj v X = Classical.choose h := by
    unfold overlapObject
    exact dif_pos h
  rw [heq]
  exact Classical.choose_spec h

theorem overlapObject_eq_of_isClusterCandidate {v : Equiv.Perm Y} {X Z : I}
    (hZ : (D.clusterOverlap ι hinj hdisj v X Z).IsClusterCandidate (D.act X) (D.act Z)
      D.h D.scale) :
    D.overlapObject ι hinj hdisj v X = Z :=
  D.overlapObject_unique ι hinj hdisj v
    (D.overlapObject_isClusterCandidate ι hinj hdisj
      ((D.mem_overlapGood ι hinj hdisj).mpr ⟨Z, hZ⟩)) hZ

theorem exists_representingPerm (v : Equiv.Perm Y) :
    ∃ σ : Equiv.Perm I,
      (∀ X ∈ D.overlapGood ι hinj hdisj v, σ X = D.overlapObject ι hinj hdisj v X) ∧
        ∀ X, D.Connected X (σ X) :=
  D.exists_perm_of_isClusterCandidate ι hinj hdisj v (D.overlapGood ι hinj hdisj v)
    (D.overlapObject ι hinj hdisj v)
    fun _ hX ↦ D.overlapObject_isClusterCandidate ι hinj hdisj hX

/-- **The object permutation representing `v`.** -/
noncomputable def representingPerm (v : Equiv.Perm Y) : Equiv.Perm I :=
  Classical.choose (D.exists_representingPerm ι hinj hdisj v)

theorem representingPerm_eq {v : Equiv.Perm Y} {X : I}
    (hX : X ∈ D.overlapGood ι hinj hdisj v) :
    D.representingPerm ι hinj hdisj v X = D.overlapObject ι hinj hdisj v X :=
  (Classical.choose_spec (D.exists_representingPerm ι hinj hdisj v)).1 X hX

theorem representingPerm_connected (v : Equiv.Perm Y) (X : I) :
    D.Connected X (D.representingPerm ι hinj hdisj v X) :=
  (Classical.choose_spec (D.exists_representingPerm ι hinj hdisj v)).2 X

/-- **The arrow representing `v` at an object.**  The overlap arrow of `v` on
good objects, and a candidate arrow otherwise. -/
noncomputable def representingArrow (v : Equiv.Perm Y) (X : I) :
    FinitePartialBijection (D.model X) (D.model (D.representingPerm ι hinj hdisj v X)) := by
  classical
  exact if X ∈ D.overlapGood ι hinj hdisj v then
      D.clusterOverlap ι hinj hdisj v X (D.representingPerm ι hinj hdisj v X)
    else (Classical.choice (D.representingPerm_connected ι hinj hdisj v X)).1

theorem representingArrow_of_mem {v : Equiv.Perm Y} {X : I}
    (hX : X ∈ D.overlapGood ι hinj hdisj v) :
    D.representingArrow ι hinj hdisj v X =
      D.clusterOverlap ι hinj hdisj v X (D.representingPerm ι hinj hdisj v X) := by
  unfold representingArrow
  exact if_pos hX

theorem representingArrow_isClusterCandidate (v : Equiv.Perm Y) (X : I) :
    (D.representingArrow ι hinj hdisj v X).IsClusterCandidate (D.act X)
      (D.act (D.representingPerm ι hinj hdisj v X)) D.h D.scale := by
  by_cases hX : X ∈ D.overlapGood ι hinj hdisj v
  · rw [D.representingArrow_of_mem ι hinj hdisj hX]
    have h := D.overlapObject_isClusterCandidate ι hinj hdisj hX
    rw [← D.representingPerm_eq ι hinj hdisj hX] at h
    exact h
  · have hrep : D.representingArrow ι hinj hdisj v X =
        (Classical.choice (D.representingPerm_connected ι hinj hdisj v X)).1 := by
      unfold representingArrow
      exact if_neg hX
    rw [hrep]
    exact (mem_clusterCandidates _ _ _ _ _).mp
      (Classical.choice (D.representingPerm_connected ι hinj hdisj v X)).2

/-- The block arrows representing `v`. -/
noncomputable def representingArrows (v : Equiv.Perm Y) :
    BlockArrows (clusterEmbedding D ι hinj hdisj) where
  objEquiv := D.representingPerm ι hinj hdisj v
  arrow X := D.representingArrow ι hinj hdisj v X

/-- **The bisection representing `v`.** -/
noncomputable def representingBisection (v : Equiv.Perm Y) :
    FiniteGroupoid.Bisection D.presentation.Obj where
  objEquiv :=
    { toFun := fun X ↦ ⟨D.representingPerm ι hinj hdisj v X.val⟩
      invFun := fun X ↦ ⟨(D.representingPerm ι hinj hdisj v).symm X.val⟩
      left_inv := fun X ↦ by cases X; simp
      right_inv := fun X ↦ by cases X; simp }
  hom X := GroupoidPresentation.ofRep _
    (⟨D.representingArrow ι hinj hdisj v X.val,
      (mem_clusterCandidates _ _ _ _ _).mpr
        (D.representingArrow_isClusterCandidate ι hinj hdisj v X.val)⟩ :
      D.clusterData.Rep X.val (D.representingPerm ι hinj hdisj v X.val))

theorem bisectionIndexEquiv_representingBisection (v : Equiv.Perm Y) (X : I) :
    bisectionIndexEquiv (D.representingBisection ι hinj hdisj v) X =
      D.representingPerm ι hinj hdisj v X := rfl

/-- The chosen representative of every arrow of the representing bisection
lies within `2 * scale` of the representing arrow. -/
theorem twoSidedDisagreement_bisectionRep_lt (v : Equiv.Perm Y) (X : I) :
    (bisectionRep (D.representingBisection ι hinj hdisj v) X).1.twoSidedDisagreement
      (D.representingArrow ι hinj hdisj v X) < 2 * D.scale :=
  Quotient.mk_out (s := D.clusterData.nearSetoid X (D.representingPerm ι hinj hdisj v X))
    (⟨D.representingArrow ι hinj hdisj v X, (mem_clusterCandidates _ _ _ _ _).mpr
      (D.representingArrow_isClusterCandidate ι hinj hdisj v X)⟩ :
      D.clusterData.Rep X (D.representingPerm ι hinj hdisj v X))

/-- **Uniqueness through the gap.**  A candidate within `16 * scale` of the
representing arrow represents the same arrow of the representing bisection. -/
theorem representingBisection_hom_eq_ofRep (v : Equiv.Perm Y) (X : I)
    (c : FinitePartialBijection (D.model X) (D.model (D.representingPerm ι hinj hdisj v X)))
    (hc : c.IsClusterCandidate (D.act X) (D.act (D.representingPerm ι hinj hdisj v X))
      D.h D.scale)
    (hnear : c.twoSidedDisagreement (D.representingArrow ι hinj hdisj v X) <
      16 * D.scale) :
    (D.representingBisection ι hinj hdisj v).hom ⟨X⟩ =
      GroupoidPresentation.ofRep D.presentation
        (⟨c, (mem_clusterCandidates _ _ _ _ _).mpr hc⟩ :
          D.clusterData.Rep X (D.representingPerm ι hinj hdisj v X)) := by
  refine (GroupoidPresentation.ofRep_eq_ofRep_iff _ _ _).mpr ?_
  refine D.clusterData.near_of_lt_eight ?_
  show (D.representingArrow ι hinj hdisj v X).twoSidedDisagreement c < 8 * (2 * D.scale)
  rw [FinitePartialBijection.twoSidedDisagreement_comm]
  omega

/-- **Hamming distance to the represented permutation.**  The patched
representing arrows differ from `v` only off the glued domain and on the
objects outside `overlapGood v`. -/
theorem card_hammingDisagreement_representingPatch_le [DecidableEq I]
    (v : Equiv.Perm Y) :
    (hammingDisagreement (D.representingArrows ι hinj hdisj v).patch v).card ≤
      (Finset.univ \ (D.representingArrows ι hinj hdisj v).domain).card +
        ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, Fintype.card (D.model X) := by
  refine (D.representingArrows ι hinj hdisj v).card_hammingDisagreement_patch_le_of_realizes
    v (D.overlapGood ι hinj hdisj v) fun X hX ↦ ?_
  show BlockArrows.RealizesOn (D.representingArrows ι hinj hdisj v) v X
    (D.representingArrow ι hinj hdisj v X)
  rw [D.representingArrow_of_mem ι hinj hdisj hX]
  exact fun x hx ↦ D.embed_clusterOverlap_apply ι hinj hdisj v X _ x hx

/-- **Objects outside `overlapGood v` carry large defect.**  Along any object
map `π`, each object outside `overlapGood v` has forward plus inverse defect at
least `h * scale / 2` for the overlap arrow into `π X`. -/
theorem card_compl_overlapGood_mul_le [DecidableEq I] (v : Equiv.Perm Y)
    (π : I → I) :
    ((D.overlapGood ι hinj hdisj v)ᶜ.card : ℝ) * (D.h * D.scale / 2) ≤
      ∑ X, (((D.clusterOverlap ι hinj hdisj v X (π X)).equivarianceDefect
        (D.act X) (D.act (π X))).card : ℝ) +
      ∑ X, (((D.clusterOverlap ι hinj hdisj v X (π X)).symm.equivarianceDefect
        (D.act (π X)) (D.act X)).card : ℝ) := by
  have hbad : ∀ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, D.h * D.scale / 2 ≤
      (((D.clusterOverlap ι hinj hdisj v X (π X)).equivarianceDefect
        (D.act X) (D.act (π X))).card : ℝ) +
      (((D.clusterOverlap ι hinj hdisj v X (π X)).symm.equivarianceDefect
        (D.act (π X)) (D.act X)).card : ℝ) := by
    intro X hX
    rw [Finset.mem_compl] at hX
    by_contra hlt
    push Not at hlt
    have h₁ : (0 : ℝ) ≤ (((D.clusterOverlap ι hinj hdisj v X (π X)).equivarianceDefect
        (D.act X) (D.act (π X))).card : ℝ) := Nat.cast_nonneg _
    have h₂ : (0 : ℝ) ≤
        (((D.clusterOverlap ι hinj hdisj v X (π X)).symm.equivarianceDefect
          (D.act (π X)) (D.act X)).card : ℝ) := Nat.cast_nonneg _
    have hh : D.h ≤ 2 * Fintype.card L :=
      le_two_mul_card_of_hasTaggedExpansionAtScale (D.expands X) D.scale_pos
        (le_trans (by omega) (D.size X))
    exact hX ((D.mem_overlapGood ι hinj hdisj).mpr ⟨π X,
      isClusterCandidate_of_card_equivarianceDefect_lt (D.act X) (D.act (π X)) hh _
        (by linarith) (by linarith)⟩)
  calc ((D.overlapGood ι hinj hdisj v)ᶜ.card : ℝ) * (D.h * D.scale / 2)
      = ∑ _X ∈ (D.overlapGood ι hinj hdisj v)ᶜ, D.h * D.scale / 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ X ∈ (D.overlapGood ι hinj hdisj v)ᶜ,
          ((((D.clusterOverlap ι hinj hdisj v X (π X)).equivarianceDefect
            (D.act X) (D.act (π X))).card : ℝ) +
          (((D.clusterOverlap ι hinj hdisj v X (π X)).symm.equivarianceDefect
            (D.act (π X)) (D.act X)).card : ℝ)) := Finset.sum_le_sum hbad
    _ ≤ ∑ X, ((((D.clusterOverlap ι hinj hdisj v X (π X)).equivarianceDefect
            (D.act X) (D.act (π X))).card : ℝ) +
          (((D.clusterOverlap ι hinj hdisj v X (π X)).symm.equivarianceDefect
            (D.act (π X)) (D.act X)).card : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun _ _ _ ↦ add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = _ := Finset.sum_add_distrib

/-- **Total forward defect of the overlap arrows.** -/
theorem sum_card_equivarianceDefect_clusterOverlap_le (act : L → Equiv.Perm Y)
    (v : Equiv.Perm Y) (π : I → I) :
    ∑ X, ((D.clusterOverlap ι hinj hdisj v X (π X)).equivarianceDefect
        (D.act X) (D.act (π X))).card ≤
      Fintype.card L * ∑ X, (D.clusterOverlap ι hinj hdisj v X (π X)).sourceDefect +
        ∑ s, ((clusterAction (ι := ι) (hinj := hinj) (hdisj := hdisj) (D := D)
          act).overlapFailure v s).card :=
  (clusterAction (ι := ι) (hinj := hinj) (hdisj := hdisj) (D := D)
    act).sum_card_equivarianceDefect_overlapArrow_le v π

/-- **Total inverse defect of the overlap arrows.** -/
theorem sum_card_symm_equivarianceDefect_clusterOverlap_le (act : L → Equiv.Perm Y)
    (v : Equiv.Perm Y) (π : I → I) :
    ∑ X, ((D.clusterOverlap ι hinj hdisj v X (π X)).symm.equivarianceDefect
        (D.act (π X)) (D.act X)).card ≤
      Fintype.card L * ∑ X, (D.clusterOverlap ι hinj hdisj v X (π X)).targetDefect +
        ∑ s, ((clusterAction (ι := ι) (hinj := hinj) (hdisj := hdisj) (D := D)
          act).overlapFailure v⁻¹ s).card :=
  (clusterAction (ι := ι) (hinj := hinj) (hdisj := hdisj) (D := D)
    act).sum_card_symm_equivarianceDefect_overlapArrow_le v π

end PartialClusterSystem
end GroupApproximation
