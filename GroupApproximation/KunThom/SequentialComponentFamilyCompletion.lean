import GroupApproximation.KunThom.SequentialComponentFamilyPruning
import GroupApproximation.Matching.Localization
import GroupApproximation.Matching.DirectedCoarea
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Completing pruned label actions

After `exists_prune` removes a set `U`, the labels are completed to
permutations of the remaining points.  This module proves the finite facts that
the sequential component family needs about those completions.

* `completion_hasCheegerLowerBound`: the completed labels of a finite set `T`
  have the directed Cheeger bound `h / (8 |T|)`.
* `card_completion_multiplicationError_le`: a completed product failure is an
  ambient product failure, or one of three images lies in `U`.
* `card_completion_disagreement_le`: a completion differs from the ambient
  permutation at most `|U|` times.
* `card_sub_le_collision_add_of_completion_eq`: two equal completions force
  ambient collisions on all but `2 |U|` of the remaining points.
* `exists_pruned_completion`: the pruning and the Cheeger bound together, for
  a generator action within edit distance `B` of an expanding graph with
  `10 B ≤ h |Y|`.
-/

namespace GroupApproximation
namespace SequentialComponentFamily

open FinitePartialBijection

/-- The finite model carried by a finset of points. -/
abbrev finsetModel (Y : FiniteModel) (C : Finset Y) : FiniteModel where
  carrier := C
  fintype := inferInstance
  decidableEq := inferInstance

variable {Y : FiniteModel}

/-- A permutation of the points of `C` that agrees with `σ` wherever `σ` stays
in `C`. -/
noncomputable def completion (C : Finset Y) (σ : Equiv.Perm Y) :
    Equiv.Perm (finsetModel Y C) :=
  Classical.choose (Localization.exists_completion C σ)

theorem completion_agrees (C : Finset Y) (σ : Equiv.Perm Y) (x : finsetModel Y C)
    (hx : σ (x : Y) ∈ C) : (completion C σ x : Y) = σ x :=
  Classical.choose_spec (Localization.exists_completion C σ) x hx

/-! ### Expansion of the completed labels -/

/-- Inner label arcs of a set of remaining points are tagged boundary arcs of
the completed labels. -/
theorem card_innerBoundary_le {L : Type*} [Fintype L] (act : L → Equiv.Perm Y)
    (U : Finset Y) (W : Finset (finsetModel Y (Finset.univ \ U))) :
    (innerBoundary act U (W.map (Function.Embedding.subtype _))).card ≤
      (taggedBoundary (fun l ↦ completion (Finset.univ \ U) (act l)) W).card := by
  classical
  refine (Finset.card_le_card ?_).trans
    (Finset.card_image_le
      (f := fun q : L × finsetModel Y (Finset.univ \ U) ↦ (q.1, (q.2 : Y))))
  intro p hp
  rw [mem_innerBoundary] at hp
  obtain ⟨hcross, hxU, hyU⟩ := hp
  have hx : p.2 ∈ Finset.univ \ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxU⟩
  have hy : act p.1 p.2 ∈ Finset.univ \ U :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyU⟩
  have hπ : completion (Finset.univ \ U) (act p.1) ⟨p.2, hx⟩ = ⟨act p.1 p.2, hy⟩ :=
    Subtype.ext (completion_agrees (Finset.univ \ U) (act p.1) ⟨p.2, hx⟩ hy)
  have hmemW : ∀ z : finsetModel Y (Finset.univ \ U),
      (z : Y) ∈ W.map (Function.Embedding.subtype _) ↔ z ∈ W :=
    fun z ↦ Finset.mem_map' (Function.Embedding.subtype _) (a := z) (s := W)
  refine Finset.mem_image.mpr ⟨(p.1, ⟨p.2, hx⟩), ?_, rfl⟩
  rw [mem_taggedBoundary]
  show (⟨p.2, hx⟩ ∈ W ∧ completion (Finset.univ \ U) (act p.1) ⟨p.2, hx⟩ ∉ W) ∨
    (⟨p.2, hx⟩ ∉ W ∧ completion (Finset.univ \ U) (act p.1) ⟨p.2, hx⟩ ∈ W)
  rw [hπ]
  rcases hcross with ⟨hin, hout⟩ | ⟨hout, hin⟩
  · exact Or.inl ⟨(hmemW ⟨p.2, hx⟩).mp hin,
      fun hmem ↦ hout ((hmemW ⟨act p.1 p.2, hy⟩).mpr hmem)⟩
  · exact Or.inr ⟨fun hmem ↦ hout ((hmemW ⟨p.2, hx⟩).mpr hmem),
      (hmemW ⟨act p.1 p.2, hy⟩).mp hin⟩

/-- Tagged boundary arcs of the labels of a finite set `T`, charged to the
permutations they use: each arc of the directed boundary receives at most `|T|`
of them. -/
theorem card_taggedBoundary_le_card_mul_directedBoundary {G : Type*} (T : Finset G)
    {Z : FiniteModel} (π : G → Equiv.Perm Z) (A : Finset Z) :
    (taggedBoundary (fun t : T ↦ π t.1) A).card ≤
      T.card * (AlmostAutomorphism.directedBoundary Z (T.image π) A).card := by
  classical
  refine Finset.card_le_mul_card_image_of_maps_to
    (f := fun p : T × Z ↦ (π p.1.1, p.2)) ?_ T.card ?_
  · intro p hp
    rw [mem_taggedBoundary] at hp
    rw [AlmostAutomorphism.mem_directedBoundary]
    exact ⟨Finset.mem_image_of_mem π p.1.2, hp⟩
  · intro b _
    refine le_trans (Finset.card_le_card_of_injOn (t := Finset.univ) Prod.fst ?_ ?_) ?_
    · intro p _
      exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
      have hq' := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
      have h2 := congrArg Prod.snd (hp'.trans hq'.symm)
      exact Prod.ext hpq h2
    · exact (Finset.card_univ.trans (Fintype.card_coe T)).le

/-- **Directed expansion of the completed labels.** -/
theorem completion_hasCheegerLowerBound {G : Type*} (T : Finset G) (hT : T.Nonempty)
    (act : G → Equiv.Perm Y) {U : Finset Y} {h : ℝ} (hh : 0 < h)
    (hinner : ∀ W : Finset Y, W.Nonempty → Disjoint U W →
      2 * W.card ≤ Fintype.card Y - U.card →
        h * W.card ≤ 8 * ((innerBoundary (fun t : T ↦ act t.1) U W).card : ℝ)) :
    DirectedCoarea.HasCheegerLowerBound (finsetModel Y (Finset.univ \ U))
      (T.image fun g ↦ completion (Finset.univ \ U) (act g)) (h / (8 * T.card)) := by
  have hTpos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr hT
  refine ⟨div_pos hh (mul_pos (by norm_num) hTpos), fun W hW hhalf ↦ ?_⟩
  let Wm : Finset Y := W.map (Function.Embedding.subtype _)
  have hWmne : Wm.Nonempty := by
    obtain ⟨z, hz⟩ := hW
    exact ⟨_, Finset.mem_map_of_mem _ hz⟩
  have hdisj : Disjoint U Wm := by
    rw [Finset.disjoint_left]
    intro x hxU hxW
    obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hxW
    exact (Finset.mem_sdiff.mp z.2).2 hxU
  have hcardC : Fintype.card (finsetModel Y (Finset.univ \ U)) =
      Fintype.card Y - U.card := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ U),
      Finset.card_univ]
  have hWmcard : Wm.card = W.card := Finset.card_map _
  have hhalfWm : 2 * Wm.card ≤ Fintype.card Y - U.card := by
    rw [hWmcard, ← hcardC]
    exact hhalf
  have h1 := hinner Wm hWmne hdisj hhalfWm
  rw [hWmcard] at h1
  have h2 : (innerBoundary (fun t : T ↦ act t.1) U Wm).card ≤
      (taggedBoundary (fun t : T ↦ completion (Finset.univ \ U) (act t.1)) W).card :=
    card_innerBoundary_le (fun t : T ↦ act t.1) U W
  have h3 : (taggedBoundary (fun t : T ↦ completion (Finset.univ \ U) (act t.1)) W).card ≤
      T.card * (AlmostAutomorphism.directedBoundary (finsetModel Y (Finset.univ \ U))
        (T.image fun g ↦ completion (Finset.univ \ U) (act g)) W).card :=
    card_taggedBoundary_le_card_mul_directedBoundary T
      (fun g ↦ completion (Finset.univ \ U) (act g)) W
  have h2R : ((innerBoundary (fun t : T ↦ act t.1) U Wm).card : ℝ) ≤
      (taggedBoundary (fun t : T ↦ completion (Finset.univ \ U) (act t.1)) W).card := by
    exact_mod_cast h2
  have h3R :
      ((taggedBoundary (fun t : T ↦ completion (Finset.univ \ U) (act t.1)) W).card : ℝ) ≤
        T.card * (AlmostAutomorphism.directedBoundary (finsetModel Y (Finset.univ \ U))
          (T.image fun g ↦ completion (Finset.univ \ U) (act g)) W).card := by
    exact_mod_cast h3
  rw [div_mul_eq_mul_div, div_le_iff₀ (mul_pos (by norm_num) hTpos)]
  linarith

/-! ### Product law, ambient agreement and collisions -/

/-- The points sent into `U` by a permutation are at most `|U|` many. -/
theorem card_filter_apply_mem_le (σ : Equiv.Perm Y) (U : Finset Y) :
    (Finset.univ.filter fun x : Y ↦ σ x ∈ U).card ≤ U.card := by
  refine Finset.card_le_card_of_injOn σ ?_ σ.injective.injOn
  intro x hx
  exact (Finset.mem_filter.mp hx).2

/-- A completed product failure is an ambient product failure, or one of the
three images involved lies in `U`. -/
theorem card_completion_multiplicationError_le {K : Type*} [Mul K]
    (act : K → Equiv.Perm Y) (U : Finset Y) (g h : K) :
    (Finset.univ.filter fun y : finsetModel Y (Finset.univ \ U) ↦
      completion (Finset.univ \ U) (act (g * h)) y ≠
        (completion (Finset.univ \ U) (act g) *
          completion (Finset.univ \ U) (act h)) y).card ≤
      (Finset.univ.filter fun x : Y ↦ act (g * h) x ≠ (act g * act h) x).card +
        3 * U.card := by
  have hkey : ∀ y : finsetModel Y (Finset.univ \ U), act h y ∉ U →
      (act g * act h) y ∉ U → act (g * h) y ∉ U →
        act (g * h) y = (act g * act h) y →
          completion (Finset.univ \ U) (act (g * h)) y =
            (completion (Finset.univ \ U) (act g) *
              completion (Finset.univ \ U) (act h)) y := by
    intro y h1 h2 h3 heq
    have hC1 : act h y ∈ Finset.univ \ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h1⟩
    have hC2 : act g (act h y) ∈ Finset.univ \ U :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h2⟩
    have hC3 : act (g * h) y ∈ Finset.univ \ U :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h3⟩
    have e1 : completion (Finset.univ \ U) (act h) y = ⟨act h y, hC1⟩ :=
      Subtype.ext (completion_agrees (Finset.univ \ U) (act h) y hC1)
    apply Subtype.ext
    rw [Equiv.Perm.mul_apply, e1, completion_agrees (Finset.univ \ U) (act (g * h)) y hC3,
      completion_agrees (Finset.univ \ U) (act g) ⟨act h y, hC1⟩ hC2]
    exact heq
  have hsub : (Finset.univ.filter fun y : finsetModel Y (Finset.univ \ U) ↦
      completion (Finset.univ \ U) (act (g * h)) y ≠
        (completion (Finset.univ \ U) (act g) *
          completion (Finset.univ \ U) (act h)) y).map (Function.Embedding.subtype _) ⊆
      (Finset.univ.filter fun x : Y ↦ act (g * h) x ≠ (act g * act h) x) ∪
        (Finset.univ.filter fun x : Y ↦ act h x ∈ U) ∪
        (Finset.univ.filter fun x : Y ↦ (act g * act h) x ∈ U) ∪
        (Finset.univ.filter fun x : Y ↦ act (g * h) x ∈ U) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    have hy' := (Finset.mem_filter.mp hy).2
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnot
    simp only [not_or, not_not] at hnot
    obtain ⟨⟨⟨hE, h1⟩, h2⟩, h3⟩ := hnot
    exact hy' (hkey y h1 h2 h3 hE)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map] at hcard
  have u1 := Finset.card_union_le
    ((Finset.univ.filter fun x : Y ↦ act (g * h) x ≠ (act g * act h) x) ∪
      (Finset.univ.filter fun x : Y ↦ act h x ∈ U) ∪
      (Finset.univ.filter fun x : Y ↦ (act g * act h) x ∈ U))
    (Finset.univ.filter fun x : Y ↦ act (g * h) x ∈ U)
  have u2 := Finset.card_union_le
    ((Finset.univ.filter fun x : Y ↦ act (g * h) x ≠ (act g * act h) x) ∪
      (Finset.univ.filter fun x : Y ↦ act h x ∈ U))
    (Finset.univ.filter fun x : Y ↦ (act g * act h) x ∈ U)
  have u3 := Finset.card_union_le
    (Finset.univ.filter fun x : Y ↦ act (g * h) x ≠ (act g * act h) x)
    (Finset.univ.filter fun x : Y ↦ act h x ∈ U)
  have p1 := card_filter_apply_mem_le (act h) U
  have p2 := card_filter_apply_mem_le (act g * act h) U
  have p3 := card_filter_apply_mem_le (act (g * h)) U
  omega

/-- A completion differs from the ambient permutation only where the ambient
image lies in `U`. -/
theorem card_completion_disagreement_le (U : Finset Y) (σ : Equiv.Perm Y) :
    (Finset.univ.filter fun y : finsetModel Y (Finset.univ \ U) ↦
      (completion (Finset.univ \ U) σ y : Y) ≠ σ y).card ≤ U.card := by
  refine Finset.card_le_card_of_injOn (fun y : finsetModel Y (Finset.univ \ U) ↦ σ y) ?_ ?_
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    by_contra hnot
    exact hy' (completion_agrees (Finset.univ \ U) σ y
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩))
  · intro y _ z _ hyz
    exact Subtype.ext (σ.injective hyz)

/-- If two ambient permutations have equal completions, they collide at every
remaining point whose two images avoid `U`. -/
theorem card_sub_le_collision_add_of_completion_eq (U : Finset Y) (σ τ : Equiv.Perm Y)
    (heq : completion (Finset.univ \ U) σ = completion (Finset.univ \ U) τ) :
    Fintype.card Y - U.card ≤
      (Finset.univ.filter fun x : Y ↦ σ x = τ x).card + 2 * U.card := by
  have hsub : Finset.univ \ U ⊆ (Finset.univ.filter fun x : Y ↦ σ x = τ x) ∪
      (Finset.univ.filter fun x : Y ↦ σ x ∈ U) ∪
      (Finset.univ.filter fun x : Y ↦ τ x ∈ U) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hσ : σ x ∈ U
    · exact Or.inl (Or.inr hσ)
    by_cases hτ : τ x ∈ U
    · exact Or.inr hτ
    refine Or.inl (Or.inl ?_)
    have e1 := completion_agrees (Finset.univ \ U) σ ⟨x, hx⟩
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hσ⟩)
    have e2 := completion_agrees (Finset.univ \ U) τ ⟨x, hx⟩
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hτ⟩)
    rw [heq] at e1
    exact e1.symm.trans e2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ] at hcard
  have u1 := Finset.card_union_le
    ((Finset.univ.filter fun x : Y ↦ σ x = τ x) ∪
      (Finset.univ.filter fun x : Y ↦ σ x ∈ U))
    (Finset.univ.filter fun x : Y ↦ τ x ∈ U)
  have u2 := Finset.card_union_le (Finset.univ.filter fun x : Y ↦ σ x = τ x)
    (Finset.univ.filter fun x : Y ↦ σ x ∈ U)
  have p1 := card_filter_apply_mem_le σ U
  have p2 := card_filter_apply_mem_le τ U
  omega

/-! ### Packaged pruning -/

/-- **Pruned completion of a generator action close to an expander.**  If the
generator graph of `act` is within edit distance `B` of a graph with Cheeger
constant `h`, and `10 B ≤ h |Y|`, then removing a set `U` with `h |U| ≤ 2 B`
and completing the labels on the rest gives directed Cheeger constant
`h / (8 |T|)`. -/
theorem exists_pruned_completion {G : Type} [Group G] (T : Finset G) (hT : T.Nonempty)
    (act : G → Equiv.Perm Y) (X : FiniteMultiGraph) (e : Y ≃ X.vertex) {h : ℝ}
    (hX : X.HasCheegerLowerBound h)
    (hsmall : 10 * (((generatorGraph Y T act).editDistance X e : ℕ) : ℝ) ≤
      h * Fintype.card Y) :
    ∃ U : Finset Y,
      h * U.card ≤ 2 * (((generatorGraph Y T act).editDistance X e : ℕ) : ℝ) ∧
        DirectedCoarea.HasCheegerLowerBound (finsetModel Y (Finset.univ \ U))
          (T.image fun g ↦ completion (Finset.univ \ U) (act g)) (h / (8 * T.card)) := by
  obtain ⟨U, hU, hinner⟩ := exists_prune (fun t : T ↦ act t.1) hX.1 (Nat.cast_nonneg _)
    (fun A hA hhalf ↦
      cheeger_le_two_mul_taggedBoundary_add_editDistance T act X e hX A hA hhalf)
    hsmall
  exact ⟨U, hU, completion_hasCheegerLowerBound T hT act hX.1 hinner⟩

end SequentialComponentFamily
end GroupApproximation
