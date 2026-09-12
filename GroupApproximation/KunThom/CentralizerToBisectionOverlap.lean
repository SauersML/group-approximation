import GroupApproximation.KunThom.FixedPointNormalizationComparison

/-!
# Reading block arrows off a permutation

Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4): an element of the centralizer of
`σ(Γ)` is represented by patching the arrows of a bisection of the cluster
groupoid.  For the forward direction the arrows are read off a given
permutation `v` of the ambient model.

* `BlockEmbedding.overlapArrow E v C C'`: the points of block `C` which `v`
  carries into block `C'`, with the partial bijection that `v` induces.  It
  realizes `v` on its source (`embed_overlapArrow_apply`), and its inverse is
  the overlap arrow of `v⁻¹` (`overlapArrow_symm`).
* `eq_of_overlapArrow_sourceDefect_lt`: on a block with at least `4 m` points,
  at most one block receives all but `2 m` of its points.
* `eq_of_overlapArrow_targetDefect_lt`: at most one block covers all but `2 m`
  points of a block with at least `4 m` points.
* `BlockArrows.card_hammingDisagreement_patch_le_of_realizes`: if the arrows on
  a set of blocks realize `v`, a patched permutation differs from `v` only off
  the glued domain and inside the other blocks.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

namespace BlockEmbedding

variable {Y : FiniteModel} {I : Type u} (E : BlockEmbedding Y I)

/-- Points of block `C` whose image under `v` lies in block `C'`. -/
noncomputable def overlapSource (v : Equiv.Perm Y) (C C' : I) :
    Finset (E.model C) := by
  classical
  exact Finset.univ.filter fun x ↦ ∃ z : E.model C', v (E.embed C x) = E.embed C' z

/-- Points of block `C'` reached by `v` from block `C`. -/
noncomputable def overlapTarget (v : Equiv.Perm Y) (C C' : I) :
    Finset (E.model C') := by
  classical
  exact Finset.univ.filter fun z ↦ ∃ x : E.model C, v (E.embed C x) = E.embed C' z

theorem mem_overlapSource {v : Equiv.Perm Y} {C C' : I} {x : E.model C} :
    x ∈ E.overlapSource v C C' ↔
      ∃ z : E.model C', v (E.embed C x) = E.embed C' z := by
  classical
  simp [overlapSource]

theorem mem_overlapTarget {v : Equiv.Perm Y} {C C' : I} {z : E.model C'} :
    z ∈ E.overlapTarget v C C' ↔
      ∃ x : E.model C, v (E.embed C x) = E.embed C' z := by
  classical
  simp [overlapTarget]

/-- The point of block `C'` reached from a point of `overlapSource v C C'`. -/
noncomputable def overlapValue (v : Equiv.Perm Y) (C C' : I) (x : E.model C)
    (hx : x ∈ E.overlapSource v C C') : E.model C' :=
  Classical.choose (E.mem_overlapSource.mp hx)

theorem overlapValue_spec (v : Equiv.Perm Y) (C C' : I) (x : E.model C)
    (hx : x ∈ E.overlapSource v C C') :
    v (E.embed C x) = E.embed C' (E.overlapValue v C C' x hx) :=
  Classical.choose_spec (E.mem_overlapSource.mp hx)

/-- The point of block `C` sent to a point of `overlapTarget v C C'`. -/
noncomputable def overlapPreimage (v : Equiv.Perm Y) (C C' : I) (z : E.model C')
    (hz : z ∈ E.overlapTarget v C C') : E.model C :=
  Classical.choose (E.mem_overlapTarget.mp hz)

theorem overlapPreimage_spec (v : Equiv.Perm Y) (C C' : I) (z : E.model C')
    (hz : z ∈ E.overlapTarget v C C') :
    v (E.embed C (E.overlapPreimage v C C' z hz)) = E.embed C' z :=
  Classical.choose_spec (E.mem_overlapTarget.mp hz)

/-- **The overlap arrow.**  The restriction of `v` to the points of block `C`
that it carries into block `C'`. -/
noncomputable def overlapArrow (v : Equiv.Perm Y) (C C' : I) :
    FinitePartialBijection (E.model C) (E.model C') where
  source := E.overlapSource v C C'
  target := E.overlapTarget v C C'
  equiv :=
    { toFun := fun x ↦ ⟨E.overlapValue v C C' x.1 x.2,
        E.mem_overlapTarget.mpr ⟨x.1, E.overlapValue_spec v C C' x.1 x.2⟩⟩
      invFun := fun z ↦ ⟨E.overlapPreimage v C C' z.1 z.2,
        E.mem_overlapSource.mpr ⟨z.1, E.overlapPreimage_spec v C C' z.1 z.2⟩⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply E.embed_injective C
        apply v.injective
        rw [E.overlapPreimage_spec, E.overlapValue_spec]
      right_inv := by
        intro z
        apply Subtype.ext
        apply E.embed_injective C'
        rw [← E.overlapValue_spec, E.overlapPreimage_spec] }

theorem overlapArrow_source (v : Equiv.Perm Y) (C C' : I) :
    (E.overlapArrow v C C').source = E.overlapSource v C C' := rfl

theorem overlapArrow_target (v : Equiv.Perm Y) (C C' : I) :
    (E.overlapArrow v C C').target = E.overlapTarget v C C' := rfl

/-- The overlap arrow realizes `v` on its source. -/
theorem embed_overlapArrow_apply (v : Equiv.Perm Y) (C C' : I) (x : E.model C)
    (hx : x ∈ (E.overlapArrow v C C').source) :
    E.embed C' ((E.overlapArrow v C C').apply x hx) = v (E.embed C x) :=
  (E.overlapValue_spec v C C' x hx).symm

theorem mem_overlapArrow_source_of_apply {v : Equiv.Perm Y} {C C' : I}
    {x : E.model C} {z : E.model C'} (h : v (E.embed C x) = E.embed C' z) :
    x ∈ (E.overlapArrow v C C').source :=
  E.mem_overlapSource.mpr ⟨z, h⟩

theorem overlapArrow_apply_eq_of_apply {v : Equiv.Perm Y} {C C' : I}
    {x : E.model C} {z : E.model C'} (h : v (E.embed C x) = E.embed C' z) :
    (E.overlapArrow v C C').apply x (E.mem_overlapArrow_source_of_apply h) = z :=
  E.embed_injective C' ((E.embed_overlapArrow_apply v C C' x _).trans h)

/-- The inverse of the overlap arrow of `v` is the overlap arrow of `v⁻¹`. -/
theorem overlapArrow_symm (v : Equiv.Perm Y) (C C' : I) :
    (E.overlapArrow v C C').symm = E.overlapArrow v⁻¹ C' C := by
  have hsource : (E.overlapArrow v C C').symm.source =
      (E.overlapArrow v⁻¹ C' C).source := by
    ext z
    show z ∈ E.overlapTarget v C C' ↔ z ∈ E.overlapSource v⁻¹ C' C
    rw [E.mem_overlapTarget, E.mem_overlapSource]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [← hx]
      exact v.symm_apply_apply _
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [← hx]
      exact v.apply_symm_apply _
  refine FinitePartialBijection.ext_source hsource fun z hz ↦ ?_
  apply E.embed_injective C
  rw [E.embed_overlapArrow_apply v⁻¹ C' C z]
  have hpre : v (E.embed C ((E.overlapArrow v C C').symm.apply z hz)) =
      E.embed C' z :=
    E.overlapPreimage_spec v C C' z hz
  calc E.embed C ((E.overlapArrow v C C').symm.apply z hz)
      = v⁻¹ (v (E.embed C ((E.overlapArrow v C C').symm.apply z hz))) :=
        (v.symm_apply_apply _).symm
    _ = v⁻¹ (E.embed C' z) := by rw [hpre]

/-- **At most one target block.**  On a block with at least `4 m` points, two
overlap arrows out of that block, each missing fewer than `2 m` source points,
have the same target block. -/
theorem eq_of_overlapArrow_sourceDefect_lt (v : Equiv.Perm Y) {C C₁ C₂ : I}
    {m : ℕ} (h₁ : (E.overlapArrow v C C₁).sourceDefect < 2 * m)
    (h₂ : (E.overlapArrow v C C₂).sourceDefect < 2 * m)
    (hsize : 4 * m ≤ Fintype.card (E.model C)) : C₁ = C₂ := by
  by_contra hne
  have hd : Disjoint (E.overlapArrow v C C₁).source
      (E.overlapArrow v C C₂).source := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨z₁, hz₁⟩ := E.mem_overlapSource.mp hx₁
    obtain ⟨z₂, hz₂⟩ := E.mem_overlapSource.mp hx₂
    exact hne (E.embed_disjoint C₁ C₂ z₁ z₂ (hz₁.symm.trans hz₂))
  have hunion := Finset.card_union_of_disjoint hd
  have hle := Finset.card_le_univ
    ((E.overlapArrow v C C₁).source ∪ (E.overlapArrow v C C₂).source)
  have hs₁ := Finset.card_le_univ (E.overlapArrow v C C₁).source
  have hs₂ := Finset.card_le_univ (E.overlapArrow v C C₂).source
  unfold FinitePartialBijection.sourceDefect at h₁ h₂
  omega

/-- **At most one source block.**  On a block with at least `4 m` points, two
overlap arrows into that block, each missing fewer than `2 m` target points,
have the same source block. -/
theorem eq_of_overlapArrow_targetDefect_lt (v : Equiv.Perm Y) {C C₁ C₂ : I}
    {m : ℕ} (h₁ : (E.overlapArrow v C₁ C).targetDefect < 2 * m)
    (h₂ : (E.overlapArrow v C₂ C).targetDefect < 2 * m)
    (hsize : 4 * m ≤ Fintype.card (E.model C)) : C₁ = C₂ := by
  by_contra hne
  have hd : Disjoint (E.overlapArrow v C₁ C).target
      (E.overlapArrow v C₂ C).target := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    obtain ⟨x₁, hx₁⟩ := E.mem_overlapTarget.mp hz₁
    obtain ⟨x₂, hx₂⟩ := E.mem_overlapTarget.mp hz₂
    exact hne (E.embed_disjoint C₁ C₂ x₁ x₂ (v.injective (hx₁.trans hx₂.symm)))
  have hunion := Finset.card_union_of_disjoint hd
  have hle := Finset.card_le_univ
    ((E.overlapArrow v C₁ C).target ∪ (E.overlapArrow v C₂ C).target)
  have ht₁ := Finset.card_le_univ (E.overlapArrow v C₁ C).target
  have ht₂ := Finset.card_le_univ (E.overlapArrow v C₂ C).target
  unfold FinitePartialBijection.targetDefect at h₁ h₂
  omega

end BlockEmbedding

namespace BlockArrows

variable {Y : FiniteModel} {I : Type u} {E : BlockEmbedding Y I} (β : BlockArrows E)

/-- **Patched permutation against a realized permutation.**  If the arrow of
every block in `good` realizes `v`, the patched permutation differs from `v`
only off the glued domain and inside the blocks outside `good`. -/
theorem card_hammingDisagreement_patch_le_of_realizes [Fintype I] [DecidableEq I]
    (v : Equiv.Perm Y) (good : Finset I)
    (hgood : ∀ C ∈ good, β.RealizesOn v C (β.arrow C)) :
    (hammingDisagreement β.patch v).card ≤
      (Finset.univ \ β.domain).card + ∑ C ∈ goodᶜ, Fintype.card (E.model C) := by
  have h₁ := β.card_hammingDisagreement_patch_le v
  have h₂ := β.card_arrowDisagreement_le_sum v
  have hzero : ∑ C ∈ good, (β.blockArrowDisagreement v C).card = 0 := by
    refine Finset.sum_eq_zero fun C hC ↦ ?_
    refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun x hx ↦ ?_)
    obtain ⟨hxs, hne⟩ := β.mem_blockArrowDisagreement.mp hx
    exact hne (hgood C hC x hxs)
  have hsplit : ∑ C ∈ good, (β.blockArrowDisagreement v C).card +
      ∑ C ∈ goodᶜ, (β.blockArrowDisagreement v C).card =
        ∑ C, (β.blockArrowDisagreement v C).card :=
    Finset.sum_add_sum_compl good _
  have hcompl : ∑ C ∈ goodᶜ, (β.blockArrowDisagreement v C).card ≤
      ∑ C ∈ goodᶜ, Fintype.card (E.model C) :=
    Finset.sum_le_sum fun C _ ↦ Finset.card_le_univ _
  omega

end BlockArrows

end BlockPatching
end GroupApproximation
