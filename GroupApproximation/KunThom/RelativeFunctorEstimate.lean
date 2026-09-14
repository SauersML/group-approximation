import GroupApproximation.KunThom.ComponentCountingRelativeFunctorRealization
import GroupApproximation.KunThom.ComponentCountingRelativeFunctorBlockWords

/-!
# Estimate (7) for the relative cluster functor

Kun and Thom (arXiv:2608.06222v3, Lemma 4.3) fix a compressor `t`, a permutation
`u` representing `σ(t)`, and a matching `π` of the components `Q_i` of `σ|_Γ`.
They transport an allowed arrow `b : Q_{π i} ⇢ Q_{π j}` back through the overlap
maps, improve the result, and prove

`d_{P_i}(θ(F_n [b]), m_j⁻¹ b m_i) ≤ r_n + q_n`.   (7)

The improvement is legitimate because the raw map `m_j⁻¹ b m_i` has small source,
range and equivariance defects.  In the endgame, (7) and the distance gap put `b`
close to the transported arrow of the bisection being conjugated.  This file
proves the finite counting behind both steps, for embedded blocks and bridges
realized by a permutation.  Every error is an explicit cardinality, and every
bound uses the actual defects of the arrows rather than candidate thresholds.

Identifying `P_i = u Q_i` with `Q_i` through `u`, the raw map is
`sandwich (E.bridge u⁻¹ (π i) i) (E.bridge u⁻¹ (π j) j) b`.

* `conjFailure E q A A' C s`: the points of block `C` at which `q` fails to carry
  the ambient action of `s` for `A` to the ambient action of `s` for `A'`.  These
  localized counts add up over disjoint blocks (`sum_card_conjFailure_le`).
* `symm_bridge_inv`: `(E.bridge q⁻¹ D C).symm = E.bridge q C D`.
* `card_equivarianceDefect_bridge_le_local` and
  `card_equivarianceDefect_symm_bridge_le_local`: the defects of a bridge and of
  its reverse, with block-localized conjugation failures.
* `sourceDefect_add_targetDefect_bridge_le`: the unmatched mass of a bridge is at
  most the symmetric difference of the image of `C` under `q` and `D`.
* `card_equivarianceDefect_sandwich_bridge_le`, `sourceDefect_sandwich_bridge_le`
  and `targetDefect_sandwich_bridge_le`: the defects of a transported arrow are at
  most its own defects plus the bridge terms at both ends.
* `card_equivarianceDefect_sandwich_bridge_words_le` and its reverse: the old
  blocks carry the words `ws s` representing `t s t⁻¹`, the new blocks carry the
  generators, and the arrow is charged `|S| · (missing mass + k · defect)`.
* `twoSidedDisagreement_sandwich_bridge_reference_le` and
  `twoSidedDisagreement_reference_le_of_improvement`: estimate (7) with the gap,
  transported back.  If the raw map is close to an arrow `a`, then `b` is close to
  the transport of `a` through the bridges realized by `u`, which is the reference
  arrow of `BlockEmbedding.realizesOn_sandwich_bridge`.
-/

namespace GroupApproximation
namespace RelativeFunctorEstimate

open BlockPatching FinitePartialBijection
open scoped symmDiff

universe u

variable {Y : FiniteModel} {I : Type u}

/-! ### Localized conjugation failures -/

/-- The points of block `C` at which `q` fails to carry the ambient action of the
label `s` for `A` to the ambient action of `s` for `A'`. -/
noncomputable def conjFailure {L : Type*} (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (A A' : BlockAction E L) (C : I) (s : L) : Finset (E.model C) := by
  classical
  exact Finset.univ.filter fun x ↦ q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))

theorem mem_conjFailure {L : Type*} (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (A A' : BlockAction E L) (C : I) (s : L) (x : E.model C) :
    x ∈ conjFailure E q A A' C s ↔
      q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x)) := by
  classical
  simp [conjFailure]

/-- **Localized failures add up.**  Over the disjoint blocks, the localized
conjugation failures of a label are at most the ambient conjugation failures. -/
theorem sum_card_conjFailure_le {L : Type*} [Fintype I] (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) (A A' : BlockAction E L) (s : L) :
    ∑ C, (conjFailure E q A A' C s).card ≤
      (Finset.univ.filter fun y : Y ↦ q (A.act s y) ≠ A'.act s (q y)).card := by
  have hsigma : (Finset.univ.sigma fun C ↦ conjFailure E q A A' C s).card =
      ∑ C, (conjFailure E q A A' C s).card :=
    Finset.card_sigma _ _
  rw [← hsigma]
  refine Finset.card_le_card_of_injOn (fun d : Σ C, E.model C ↦ E.embed d.1 d.2) ?_ ?_
  · rintro ⟨C, x⟩ hd
    have hx := (Finset.mem_sigma.mp (Finset.mem_coe.mp hd)).2
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    exact (mem_conjFailure E q A A' C s x).mp hx
  · rintro ⟨C, x⟩ - ⟨C', x'⟩ - h
    obtain rfl := E.embed_disjoint C C' x x' h
    obtain rfl := E.embed_injective C h
    rfl

/-! ### Reversing bridges -/

/-- The reverse of the bridge realized by `q⁻¹` from `D` to `C` is the bridge
realized by `q` from `C` to `D`. -/
theorem symm_bridge_inv (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q⁻¹ D C).symm = E.bridge q C D := by
  have hs : (E.bridge q⁻¹ D C).symm.source = (E.bridge q C D).source := by
    ext x
    change x ∈ E.bridgeTarget q⁻¹ D C ↔ x ∈ E.bridgeSource q C D
    rw [E.mem_bridgeTarget, E.mem_bridgeSource, inv_inv]
  have ht : (E.bridge q⁻¹ D C).symm.target = (E.bridge q C D).target := by
    ext z
    change z ∈ E.bridgeSource q⁻¹ D C ↔ z ∈ E.bridgeTarget q C D
    rw [E.mem_bridgeSource, E.mem_bridgeTarget]
  refine FinitePartialBijection.ext hs ht fun x hx ↦ ?_
  apply E.embed_injective D
  rw [E.embed_bridge_symm_apply, E.embed_bridge_apply, inv_inv]

/-- The reverse of the bridge realized by `q` is the bridge realized by `q⁻¹`. -/
theorem symm_bridge (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q C D).symm = E.bridge q⁻¹ D C := by
  have h := symm_bridge_inv E q⁻¹ D C
  rw [inv_inv] at h
  exact h

theorem sourceDefect_bridge_inv (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q⁻¹ D C).sourceDefect = (E.bridge q C D).targetDefect := by
  have h := congrArg FinitePartialBijection.targetDefect (symm_bridge_inv E q C D)
  exact h

theorem targetDefect_bridge_inv (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q⁻¹ D C).targetDefect = (E.bridge q C D).sourceDefect := by
  have h := congrArg FinitePartialBijection.sourceDefect (symm_bridge_inv E q C D)
  exact h

/-! ### Localized bridge defects -/

/-- **One label, localized.**  The defect of a bridge at label `s` is at most its
missing source mass, the compatibility failures of both block actions at `s`, and
the points of the source block at which `q` fails to conjugate `A.act s` into
`A'.act s`. -/
theorem card_bridge_labelSlice_le_local {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) (A A' : BlockAction E L) (s : L) :
    (Finset.univ.filter fun x : E.model C ↦
        (s, x) ∈ (E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)).card ≤
      (E.bridge q C D).sourceDefect + (A.compatFailure C s).card +
        (conjFailure E q A A' C s).card + (A'.compatFailure D s).card := by
  have hsub : (Finset.univ.filter fun x : E.model C ↦
        (s, x) ∈ (E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)) ⊆
      ((Finset.univ \ (E.bridge q C D).source) ∪ A.compatFailure C s) ∪
        conjFailure E q A A' C s ∪
        (Finset.univ.filter fun x : E.model C ↦
          q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D)) := by
    intro x hx
    by_cases h₀ : x ∈ (E.bridge q C D).source
    swap
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h₀⟩)))
    by_cases h₁ : x ∈ A.compatFailure C s
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h₁))
    by_cases h₂ : q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        ((mem_conjFailure E q A A' C s x).mpr h₂))
    by_cases h₃ : q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₃⟩)
    exfalso
    push Not at h₂
    have hdef := (Finset.mem_filter.mp hx).2
    rw [mem_equivarianceDefect] at hdef
    dsimp only at hdef
    have hz := E.embed_bridge_apply q C D x h₀
    have hcompatC := A.embed_blockAct_of_not_mem h₁
    have hnotD : (E.bridge q C D).apply x h₀ ∉ A'.compatFailure D s := by
      intro hmem
      apply h₃
      rw [← hz]
      exact Finset.mem_image_of_mem _ hmem
    have hcompatD := A'.embed_blockAct_of_not_mem hnotD
    have hkey : E.embed D (A'.blockAct D s ((E.bridge q C D).apply x h₀)) =
        q (E.embed C (A.blockAct C s x)) := by
      rw [hcompatD, hz, hcompatC, h₂]
    have hsrc : A.blockAct C s x ∈ (E.bridge q C D).source :=
      (E.mem_bridgeSource q C D _).mpr ⟨_, hkey⟩
    apply hdef h₀ hsrc
    apply E.embed_injective D
    rw [E.embed_bridge_apply q C D _ hsrc, hkey]
  have hcard := Finset.card_le_card hsub
  have hu₁ := Finset.card_union_le
    (((Finset.univ \ (E.bridge q C D).source) ∪ A.compatFailure C s) ∪
      conjFailure E q A A' C s)
    (Finset.univ.filter fun x : E.model C ↦
      q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D))
  have hu₂ := Finset.card_union_le
    ((Finset.univ \ (E.bridge q C D).source) ∪ A.compatFailure C s)
    (conjFailure E q A A' C s)
  have hu₃ := Finset.card_union_le (Finset.univ \ (E.bridge q C D).source)
    (A.compatFailure C s)
  have hsd : (Finset.univ \ (E.bridge q C D).source).card ≤ (E.bridge q C D).sourceDefect := by
    have hsplit := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (E.bridge q C D).source)
    rw [Finset.card_univ] at hsplit
    unfold FinitePartialBijection.sourceDefect
    omega
  have hpull : (Finset.univ.filter fun x : E.model C ↦
        q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D)).card ≤
      (A'.compatFailure D s).card := by
    refine le_trans ?_ (Finset.card_image_le (s := A'.compatFailure D s) (f := E.embed D))
    apply Finset.card_le_card_of_injOn (fun x ↦ q (E.embed C x))
    · intro x hx
      rw [Finset.mem_coe] at hx ⊢
      exact (Finset.mem_filter.mp hx).2
    · intro x _ x' _ hxx'
      exact E.embed_injective C (q.injective hxx')
  omega

/-- **Localized bridge defect.**  The equivariance defect of a bridge is at most,
summed over labels, its missing source mass, the compatibility failures of both
block actions, and the localized conjugation failures of `q`. -/
theorem card_equivarianceDefect_bridge_le_local {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) (A A' : BlockAction E L) :
    ((E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)).card ≤
      ∑ s : L, ((E.bridge q C D).sourceDefect + (A.compatFailure C s).card +
        (conjFailure E q A A' C s).card + (A'.compatFailure D s).card) :=
  (BlockEmbedding.card_le_sum_labelSlices _).trans
    (Finset.sum_le_sum fun s _ ↦ card_bridge_labelSlice_le_local E q C D A A' s)

/-- **Localized defect of a reversed bridge.**  The reverse of the bridge realized
by `q` is realized by `q⁻¹`, so its defect is controlled by the missing range mass
of the bridge and the localized conjugation failures of `q⁻¹` on the target
block. -/
theorem card_equivarianceDefect_symm_bridge_le_local {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) (A A' : BlockAction E L) :
    ((E.bridge q C D).symm.equivarianceDefect (A'.blockAct D) (A.blockAct C)).card ≤
      ∑ s : L, ((E.bridge q C D).targetDefect + (A'.compatFailure D s).card +
        (conjFailure E q⁻¹ A' A D s).card + (A.compatFailure C s).card) := by
  have h := card_equivarianceDefect_bridge_le_local E q⁻¹ D C A' A
  rw [sourceDefect_bridge_inv E q C D] at h
  rw [symm_bridge E q C D]
  exact h

/-! ### Unmatched mass of a bridge -/

/-- The missing source mass of a bridge is at most the number of points of the
image of `C` under `q` outside `D`. -/
theorem sourceDefect_bridge_le (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q C D).sourceDefect ≤
      ((Finset.univ.image fun x : E.model C ↦ q (E.embed C x)) \
        Finset.univ.image (E.embed D)).card := by
  have hmaps : (Finset.univ \ (E.bridge q C D).source).card ≤
      ((Finset.univ.image fun x : E.model C ↦ q (E.embed C x)) \
        Finset.univ.image (E.embed D)).card := by
    apply Finset.card_le_card_of_injOn (fun x : E.model C ↦ q (E.embed C x))
    · intro x hx
      rw [Finset.mem_coe] at hx ⊢
      have hxs : x ∉ (E.bridge q C D).source := (Finset.mem_sdiff.mp hx).2
      rw [BlockEmbedding.bridge_source, E.mem_bridgeSource] at hxs
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, ?_⟩
      intro himg
      obtain ⟨z, -, hz⟩ := Finset.mem_image.mp himg
      have hz' : E.embed D z = q (E.embed C x) := hz
      exact hxs ⟨z, hz'⟩
    · intro x _ x' _ hxx'
      exact E.embed_injective C (q.injective hxx')
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (E.bridge q C D).source)
  rw [Finset.card_univ] at hsplit
  unfold FinitePartialBijection.sourceDefect
  omega

/-- The missing range mass of a bridge is at most the number of points of `D`
outside the image of `C` under `q`. -/
theorem targetDefect_bridge_le (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q C D).targetDefect ≤
      (Finset.univ.image (E.embed D) \
        Finset.univ.image fun x : E.model C ↦ q (E.embed C x)).card := by
  have hmaps : (Finset.univ \ (E.bridge q C D).target).card ≤
      (Finset.univ.image (E.embed D) \
        Finset.univ.image fun x : E.model C ↦ q (E.embed C x)).card := by
    apply Finset.card_le_card_of_injOn (E.embed D)
    · intro z hz
      rw [Finset.mem_coe] at hz ⊢
      have hzt : z ∉ (E.bridge q C D).target := (Finset.mem_sdiff.mp hz).2
      change z ∉ E.bridgeTarget q C D at hzt
      rw [E.mem_bridgeTarget] at hzt
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩, ?_⟩
      intro himg
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp himg
      have hx' : q (E.embed C x) = E.embed D z := hx
      refine hzt ⟨x, ?_⟩
      rw [← hx', Equiv.Perm.coe_inv, q.symm_apply_apply]
    · intro z _ z' _ hzz'
      exact E.embed_injective D hzz'
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (E.bridge q C D).target)
  rw [Finset.card_univ] at hsplit
  unfold FinitePartialBijection.targetDefect
  omega

/-- **Unmatched mass of a bridge.**  The missing source and range masses of a
bridge together are at most the symmetric difference of the image of `C` under
`q` and `D`. -/
theorem sourceDefect_add_targetDefect_bridge_le (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (C D : I) :
    (E.bridge q C D).sourceDefect + (E.bridge q C D).targetDefect ≤
      ((Finset.univ.image fun x : E.model C ↦ q (E.embed C x)) ∆
        Finset.univ.image (E.embed D)).card := by
  have h₁ := sourceDefect_bridge_le E q C D
  have h₂ := targetDefect_bridge_le E q C D
  have hunion := Finset.card_union_add_card_inter
    ((Finset.univ.image fun x : E.model C ↦ q (E.embed C x)) \
      Finset.univ.image (E.embed D))
    (Finset.univ.image (E.embed D) \
      Finset.univ.image fun x : E.model C ↦ q (E.embed C x))
  have hinter : ((Finset.univ.image fun x : E.model C ↦ q (E.embed C x)) \
        Finset.univ.image (E.embed D)) ∩
      (Finset.univ.image (E.embed D) \
        Finset.univ.image fun x : E.model C ↦ q (E.embed C x)) = ∅ := by
    ext y
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.notMem_empty, iff_false]
    rintro ⟨⟨-, hy⟩, hy', -⟩
    exact hy hy'
  have hsub := Finset.card_le_card (Finset.union_subset
    (Finset.symmDiff_subset_sdiff (s := Finset.univ.image fun x : E.model C ↦ q (E.embed C x))
      (t := Finset.univ.image (E.embed D)))
    Finset.symmDiff_subset_sdiff')
  rw [hinter, Finset.card_empty] at hunion
  omega

/-! ### Defects of a transported arrow -/

/-- **Transported equivariance defect.**  Transport an arrow `f : C ⇢ D` through
the bridges realized by `q` into `C'` and `D'`, with label families `A` on the old
blocks and `A'` on the new ones.  Its defect is at most the defect of `f` plus the
localized bridge terms at both ends. -/
theorem card_equivarianceDefect_sandwich_bridge_le {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C C' D D' : I) (A A' : BlockAction E L)
    (f : FinitePartialBijection (E.model C) (E.model D)) :
    ((sandwich (E.bridge q C C') (E.bridge q D D') f).equivarianceDefect
        (A'.blockAct C') (A'.blockAct D')).card ≤
      ∑ s : L, ((E.bridge q C C').targetDefect + (A'.compatFailure C' s).card +
        (conjFailure E q⁻¹ A' A C' s).card + (A.compatFailure C s).card) +
      (f.equivarianceDefect (A.blockAct C) (A.blockAct D)).card +
      ∑ s : L, ((E.bridge q D D').sourceDefect + (A.compatFailure D s).card +
        (conjFailure E q A A' D s).card + (A'.compatFailure D' s).card) := by
  have h₁ := card_equivarianceDefect_sandwich_le (A.blockAct C) (A'.blockAct C')
    (A.blockAct D) (A'.blockAct D') (E.bridge q C C') (E.bridge q D D') f
  have h₂ := card_equivarianceDefect_symm_bridge_le_local E q C C' A A'
  have h₃ := card_equivarianceDefect_bridge_le_local E q D D' A A'
  omega

/-- **Transported source mass.** -/
theorem sourceDefect_sandwich_bridge_le (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (C C' D D' : I) (f : FinitePartialBijection (E.model C) (E.model D)) :
    (sandwich (E.bridge q C C') (E.bridge q D D') f).sourceDefect ≤
      (E.bridge q C C').targetDefect + f.sourceDefect + (E.bridge q D D').sourceDefect := by
  have h₁ := sourceDefect_trans_le ((E.bridge q C C').symm.trans f) (E.bridge q D D')
  have h₂ := sourceDefect_trans_le (E.bridge q C C').symm f
  have h₃ := sourceDefect_symm (E.bridge q C C')
  unfold sandwich
  omega

/-- **Transported range mass.** -/
theorem targetDefect_sandwich_bridge_le (E : BlockEmbedding Y I) (q : Equiv.Perm Y)
    (C C' D D' : I) (f : FinitePartialBijection (E.model C) (E.model D)) :
    (sandwich (E.bridge q C C') (E.bridge q D D') f).targetDefect ≤
      (E.bridge q D D').targetDefect + f.targetDefect + (E.bridge q C C').sourceDefect := by
  have h₁ := targetDefect_trans_le ((E.bridge q C C').symm.trans f) (E.bridge q D D')
  have h₂ := targetDefect_trans_le (E.bridge q C C').symm f
  have h₃ := targetDefect_symm (E.bridge q C C')
  unfold sandwich
  omega

/-! ### Word labels -/

/-- The labels acting through the words `ws s` in the labels of `A`, on the
ambient model and on every block. -/
def wordBlockAction {E : BlockEmbedding Y I} {L L' : Type*} (A : BlockAction E L)
    (ws : L' → List L) : BlockAction E L' where
  act s := wordAct A.act (ws s)
  blockAct C s := wordAct (A.blockAct C) (ws s)

theorem mem_compatFailure {E : BlockEmbedding Y I} {L : Type*} (A : BlockAction E L)
    (C : I) (s : L) (x : E.model C) :
    x ∈ A.compatFailure C s ↔ E.embed C (A.blockAct C s x) ≠ A.act s (E.embed C x) := by
  classical
  simp [BlockAction.compatFailure]

/-- The compatibility failures of a word label are the compatibility failures of
its word. -/
theorem compatFailure_wordBlockAction {E : BlockEmbedding Y I} {L L' : Type*}
    (A : BlockAction E L) (ws : L' → List L) (C : I) (s : L') :
    (wordBlockAction A ws).compatFailure C s = A.wordCompatFailure C (ws s) :=
  Finset.ext fun x ↦ (mem_compatFailure (wordBlockAction A ws) C s x).trans
    (A.mem_wordCompatFailure C (ws s) x).symm

/-- **The raw map of the relative functor.**  Transport an arrow `f : C ⇢ D`
through the bridges realized by `q` into `C'` and `D'`, where the old blocks carry
the words `ws s` and the new blocks carry the labels `s` themselves.  For the
functor of Kun--Thom Lemma 4.3, `q = u⁻¹` and `ws s` represents `t s t⁻¹`.  The
defect is at most the localized bridge terms plus `|S| · (sourceDefect f + k ·
defect f)` for words of length at most `k`. -/
theorem card_equivarianceDefect_sandwich_bridge_words_le {S : Type*} [Fintype S]
    [DecidableEq S] (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C C' D D' : I)
    (A : BlockAction E S) (ws : S → List S) {k : ℕ} (hk : ∀ s, (ws s).length ≤ k)
    (f : FinitePartialBijection (E.model C) (E.model D)) :
    ((sandwich (E.bridge q C C') (E.bridge q D D') f).equivarianceDefect
        (A.blockAct C') (A.blockAct D')).card ≤
      ∑ s : S, ((E.bridge q C C').targetDefect + (A.compatFailure C' s).card +
        (conjFailure E q⁻¹ A (wordBlockAction A ws) C' s).card +
          (A.wordCompatFailure C (ws s)).card) +
      Fintype.card S *
        (f.sourceDefect + k * (f.equivarianceDefect (A.blockAct C) (A.blockAct D)).card) +
      ∑ s : S, ((E.bridge q D D').sourceDefect + (A.wordCompatFailure D (ws s)).card +
        (conjFailure E q (wordBlockAction A ws) A D s).card + (A.compatFailure D' s).card) := by
  have h₁ := card_equivarianceDefect_sandwich_bridge_le E q C C' D D'
    (wordBlockAction A ws) A f
  have h₂ : (f.equivarianceDefect ((wordBlockAction A ws).blockAct C)
      ((wordBlockAction A ws).blockAct D)).card ≤
        Fintype.card S *
          (f.sourceDefect + k * (f.equivarianceDefect (A.blockAct C) (A.blockAct D)).card) :=
    card_equivarianceDefect_wordAct_le f (A.blockAct C) (A.blockAct D) ws hk
  have h₃ : ∑ s : S, ((E.bridge q C C').targetDefect + (A.compatFailure C' s).card +
        (conjFailure E q⁻¹ A (wordBlockAction A ws) C' s).card +
          ((wordBlockAction A ws).compatFailure C s).card) =
      ∑ s : S, ((E.bridge q C C').targetDefect + (A.compatFailure C' s).card +
        (conjFailure E q⁻¹ A (wordBlockAction A ws) C' s).card +
          (A.wordCompatFailure C (ws s)).card) :=
    Finset.sum_congr rfl fun s _ ↦ by simp only [compatFailure_wordBlockAction]
  have h₄ : ∑ s : S, ((E.bridge q D D').sourceDefect +
        ((wordBlockAction A ws).compatFailure D s).card +
        (conjFailure E q (wordBlockAction A ws) A D s).card + (A.compatFailure D' s).card) =
      ∑ s : S, ((E.bridge q D D').sourceDefect + (A.wordCompatFailure D (ws s)).card +
        (conjFailure E q (wordBlockAction A ws) A D s).card + (A.compatFailure D' s).card) :=
    Finset.sum_congr rfl fun s _ ↦ by simp only [compatFailure_wordBlockAction]
  omega

/-- **The reverse of the raw map.**  The same bound for the inverse of the
transported arrow, charged to the missing range mass and the backward defect of
`f`. -/
theorem card_symm_equivarianceDefect_sandwich_bridge_words_le {S : Type*} [Fintype S]
    [DecidableEq S] (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C C' D D' : I)
    (A : BlockAction E S) (ws : S → List S) {k : ℕ} (hk : ∀ s, (ws s).length ≤ k)
    (f : FinitePartialBijection (E.model C) (E.model D)) :
    ((sandwich (E.bridge q C C') (E.bridge q D D') f).symm.equivarianceDefect
        (A.blockAct D') (A.blockAct C')).card ≤
      ∑ s : S, ((E.bridge q D D').targetDefect + (A.compatFailure D' s).card +
        (conjFailure E q⁻¹ A (wordBlockAction A ws) D' s).card +
          (A.wordCompatFailure D (ws s)).card) +
      Fintype.card S *
        (f.targetDefect + k * (f.symm.equivarianceDefect (A.blockAct D) (A.blockAct C)).card) +
      ∑ s : S, ((E.bridge q C C').sourceDefect + (A.wordCompatFailure C (ws s)).card +
        (conjFailure E q (wordBlockAction A ws) A C s).card + (A.compatFailure C' s).card) := by
  rw [sandwich_symm]
  exact card_equivarianceDefect_sandwich_bridge_words_le E q D D' C C' A ws hk f.symm

/-! ### Estimate (7) with the gap, transported back -/

/-- **Transport back.**  Let `c` be the raw map of the relative functor on `b`,
the transport of `b` through the bridges realized by `u⁻¹`.  Then `b` is close to
the transport of any arrow `a` through the bridges realized by `u`, up to the
unmatched mass of the two bridges realized by `u`, the missing mass of `b`, and
the distance from `c` to `a`. -/
theorem twoSidedDisagreement_sandwich_bridge_reference_le (E : BlockEmbedding Y I)
    (u : Equiv.Perm Y) (i i' j j' : I)
    (b : FinitePartialBijection (E.model i') (E.model j'))
    (a : FinitePartialBijection (E.model i) (E.model j)) :
    b.twoSidedDisagreement (sandwich (E.bridge u i i') (E.bridge u j j') a) ≤
      3 * (E.bridge u i i').targetDefect + (E.bridge u i i').sourceDefect +
        (b.sourceDefect + b.targetDefect) +
        3 * (E.bridge u j j').targetDefect + (E.bridge u j j').sourceDefect +
        (sandwich (E.bridge u⁻¹ i' i) (E.bridge u⁻¹ j' j) b).twoSidedDisagreement a := by
  have hround := twoSidedDisagreement_sandwich_roundtrip_le
    (E.bridge u⁻¹ i' i) (E.bridge u⁻¹ j' j) b
  rw [symm_bridge_inv E u i i', symm_bridge_inv E u j j', sourceDefect_bridge_inv E u i i',
    sourceDefect_bridge_inv E u j j'] at hround
  have hlip := twoSidedDisagreement_sandwich_le (E.bridge u i i') (E.bridge u j j')
    (sandwich (E.bridge u⁻¹ i' i) (E.bridge u⁻¹ j' j) b) a
  have htri := twoSidedDisagreement_le b
    (sandwich (E.bridge u i i') (E.bridge u j j')
      (sandwich (E.bridge u⁻¹ i' i) (E.bridge u⁻¹ j' j) b))
    (sandwich (E.bridge u i i') (E.bridge u j j') a)
  have hcomm := twoSidedDisagreement_comm b
    (sandwich (E.bridge u i i') (E.bridge u j j')
      (sandwich (E.bridge u⁻¹ i' i) (E.bridge u⁻¹ j' j) b))
  omega

/-- **Estimate (7) with the gap.**  If an improvement `r` of the raw map lies
within `ρ` of it, and `r` lies within `κ` of an arrow `a` in the same cluster, then
`b` lies within the bridge and missing-mass terms plus `ρ + κ` of the reference
arrow transported from `a`. -/
theorem twoSidedDisagreement_reference_le_of_improvement (E : BlockEmbedding Y I)
    (u : Equiv.Perm Y) (i i' j j' : I)
    (b : FinitePartialBijection (E.model i') (E.model j'))
    (a r : FinitePartialBijection (E.model i) (E.model j)) {ρ κ : ℕ}
    (hρ : r.twoSidedDisagreement (sandwich (E.bridge u⁻¹ i' i) (E.bridge u⁻¹ j' j) b) ≤ ρ)
    (hκ : r.twoSidedDisagreement a ≤ κ) :
    b.twoSidedDisagreement (sandwich (E.bridge u i i') (E.bridge u j j') a) ≤
      3 * (E.bridge u i i').targetDefect + (E.bridge u i i').sourceDefect +
        (b.sourceDefect + b.targetDefect) +
        3 * (E.bridge u j j').targetDefect + (E.bridge u j j').sourceDefect + (ρ + κ) := by
  have h := twoSidedDisagreement_sandwich_bridge_reference_le E u i i' j j' b a
  have htri := twoSidedDisagreement_le
    (sandwich (E.bridge u⁻¹ i' i) (E.bridge u⁻¹ j' j) b) r a
  have hcomm := twoSidedDisagreement_comm
    (sandwich (E.bridge u⁻¹ i' i) (E.bridge u⁻¹ j' j) b) r
  omega

end RelativeFunctorEstimate
end GroupApproximation
