import GroupApproximation.Matching.FinitePartialBijection

/-!
# Patching block arrows into a permutation

A partition of a finite model into blocks, a permutation of the blocks, and
one partial bijection from every block into its image block glue to a
partial bijection of the whole model, which extends to a permutation `patch`.

Two counts control `patch`.

* `card_hammingDisagreement_patch_le`: `patch` disagrees with a permutation
  `w` only off the glued domain, or at a point where the arrow of its block
  disagrees with `w`.
* `card_commutationDefect_patch_le`: for a labelled action preserving every
  block, `patch` fails to commute with a label only off the glued domain, at a
  point the label moves off the domain, or at a point of the equivariance
  defect of its block arrow.

These are the finite estimates used to pass from a bisection of a cluster
groupoid back to a permutation of the model (Kun--Thom, arXiv:2608.06222v3,
proof of Theorem 4.1): the first compares a patched bisection with a
conjugate permutation, and the second shows that a patched bisection of
almost equivariant arrows almost commutes with the labelled action.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

/-- Pairwise disjoint blocks inside a finite model, each presented as a finite
model of its own. -/
structure BlockEmbedding (Y : FiniteModel) (I : Type u) where
  /-- The block with index `C`. -/
  model : I → FiniteModel
  /-- The inclusion of a block into the ambient model. -/
  embed : ∀ C, model C → Y
  embed_injective : ∀ C, Function.Injective (embed C)
  embed_disjoint : ∀ (C D : I) (x : model C) (z : model D),
    embed C x = embed D z → C = D

/-- A permutation of the blocks together with a partial bijection from every
block into its image block. -/
structure BlockArrows {Y : FiniteModel} {I : Type u} (E : BlockEmbedding Y I) where
  /-- The permutation of block indices. -/
  objEquiv : I ≃ I
  /-- The arrow from block `C` into block `objEquiv C`. -/
  arrow : ∀ C, FinitePartialBijection (E.model C) (E.model (objEquiv C))

/-- A labelled action of the ambient model which preserves every block. -/
structure BlockAction {Y : FiniteModel} {I : Type u} (E : BlockEmbedding Y I)
    (L : Type*) where
  /-- The ambient action of the labels. -/
  act : L → Equiv.Perm Y
  /-- The restriction of the action to a block. -/
  blockAct : ∀ C, L → Equiv.Perm (E.model C)
  embed_blockAct : ∀ C s x, E.embed C (blockAct C s x) = act s (E.embed C x)

namespace BlockArrows

variable {Y : FiniteModel} {I : Type u} [Fintype I]
variable {E : BlockEmbedding Y I} (β : BlockArrows E)

/-- Points of the glued domain, recorded together with their block. -/
abbrev Dom := Σ C : I, ↥(β.arrow C).source

/-- A glued-domain point, read in the ambient model. -/
def domIncl (d : β.Dom) : Y := E.embed d.1 d.2.1

/-- The image of a glued-domain point under the arrow of its block. -/
def domTarget (d : β.Dom) : Y :=
  E.embed (β.objEquiv d.1) ((β.arrow d.1).apply d.2.1 d.2.2)

theorem domIncl_injective : Function.Injective β.domIncl := by
  rintro ⟨C, x, hx⟩ ⟨D, z, hz⟩ h
  have hCD : C = D := E.embed_disjoint C D x z h
  subst hCD
  have hxz : x = z := E.embed_injective _ h
  subst hxz
  rfl

theorem domTarget_injective : Function.Injective β.domTarget := by
  rintro ⟨C, x, hx⟩ ⟨D, z, hz⟩ h
  have hCD : C = D := β.objEquiv.injective
    (E.embed_disjoint (β.objEquiv C) (β.objEquiv D)
      ((β.arrow C).apply x hx) ((β.arrow D).apply z hz) h)
  subst hCD
  have happ : (β.arrow _).apply x hx = (β.arrow _).apply z hz :=
    E.embed_injective _ h
  have hxz : x = z := (β.arrow _).apply_injective hx hz happ
  subst hxz
  rfl

theorem exists_patch :
    ∃ p : Equiv.Perm Y, ∀ d : β.Dom, p (β.domIncl d) = β.domTarget d :=
  Equiv.Perm.exists_extending_pair β.domIncl β.domTarget
    β.domIncl_injective β.domTarget_injective

/-- The patched permutation.  It agrees with the arrow of every block on the
source of that arrow, and is an arbitrary bijection elsewhere. -/
noncomputable def patch : Equiv.Perm Y := Classical.choose β.exists_patch

theorem patch_domIncl (d : β.Dom) : β.patch (β.domIncl d) = β.domTarget d :=
  Classical.choose_spec β.exists_patch d

theorem patch_embed (C : I) (x : E.model C) (hx : x ∈ (β.arrow C).source) :
    β.patch (E.embed C x) = E.embed (β.objEquiv C) ((β.arrow C).apply x hx) :=
  β.patch_domIncl ⟨C, x, hx⟩

/-- The glued domain inside the ambient model. -/
noncomputable def domain : Finset Y := Finset.univ.image β.domIncl

theorem mem_domain {y : Y} : y ∈ β.domain ↔ ∃ d : β.Dom, β.domIncl d = y := by
  simp [domain]

/-- The glued domain has exactly the total source mass of the arrows. -/
theorem card_domain : β.domain.card = ∑ C, (β.arrow C).source.card := by
  rw [domain, Finset.card_image_of_injective _ β.domIncl_injective,
    Finset.card_univ, Fintype.card_sigma]
  simp

/-- Glued-domain points at which the arrow of the block disagrees with `w`. -/
noncomputable def arrowDisagreement (w : Equiv.Perm Y) : Finset β.Dom := by
  classical
  exact Finset.univ.filter fun d ↦ β.domTarget d ≠ w (β.domIncl d)

theorem mem_arrowDisagreement {w : Equiv.Perm Y} {d : β.Dom} :
    d ∈ β.arrowDisagreement w ↔ β.domTarget d ≠ w (β.domIncl d) := by
  simp [arrowDisagreement]

/-- **Patched disagreement.**  A patched permutation disagrees with `w` only
off the glued domain or where the arrow of the block disagrees with `w`. -/
theorem card_hammingDisagreement_patch_le (w : Equiv.Perm Y) :
    (hammingDisagreement β.patch w).card ≤
      (Finset.univ \ β.domain).card + (β.arrowDisagreement w).card := by
  classical
  have hsplit := Finset.card_sdiff_add_card_inter
    (hammingDisagreement β.patch w) β.domain
  have hleft : (hammingDisagreement β.patch w \ β.domain).card ≤
      (Finset.univ \ β.domain).card :=
    Finset.card_le_card
      (Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _))
  have hsub : hammingDisagreement β.patch w ∩ β.domain ⊆
      (β.arrowDisagreement w).image β.domIncl := by
    intro y hy
    rw [Finset.mem_inter] at hy
    obtain ⟨hys, hyd⟩ := hy
    obtain ⟨d, hd⟩ := β.mem_domain.mp hyd
    rw [Finset.mem_image]
    refine ⟨d, ?_, hd⟩
    rw [β.mem_arrowDisagreement, ← β.patch_domIncl d, hd]
    exact (mem_hammingDisagreement _ _ _).mp hys
  have hright : (hammingDisagreement β.patch w ∩ β.domain).card ≤
      (β.arrowDisagreement w).card :=
    (Finset.card_le_card hsub).trans Finset.card_image_le
  omega

/-- The glued-domain points of block `C` lying in the equivariance defect of
the block arrow at label `s`. -/
noncomputable def labelDefect {L : Type*} [Fintype L] (A : BlockAction E L)
    (s : L) : Finset β.Dom := by
  classical
  exact Finset.univ.sigma fun C ↦ (β.arrow C).source.attach.filter fun x ↦
    (s, x.1) ∈ (β.arrow C).equivarianceDefect (A.blockAct C)
      (A.blockAct (β.objEquiv C))

/-- The label defect is bounded by the total equivariance defect. -/
theorem card_labelDefect_le {L : Type*} [Fintype L] (A : BlockAction E L)
    (s : L) :
    (β.labelDefect A s).card ≤
      ∑ C, ((β.arrow C).equivarianceDefect (A.blockAct C)
        (A.blockAct (β.objEquiv C))).card := by
  classical
  rw [labelDefect, Finset.card_sigma]
  refine Finset.sum_le_sum fun C _ ↦ ?_
  refine Finset.card_le_card_of_injOn (fun x ↦ (s, x.1)) ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x _ z _ hxz
    exact Subtype.ext (congrArg Prod.snd hxz)

/-- **Patched commutation.**  For a labelled action preserving every block, a
patched permutation fails to commute with a label only off the glued domain,
at a point the label moves off the domain, or at a point of the equivariance
defect of its block arrow. -/
theorem card_commutationDefect_patch_le {L : Type*} [Fintype L]
    (A : BlockAction E L) (s : L) :
    (hammingDisagreement (β.patch * A.act s) (A.act s * β.patch)).card ≤
      2 * (Finset.univ \ β.domain).card +
        ∑ C, ((β.arrow C).equivarianceDefect (A.blockAct C)
          (A.blockAct (β.objEquiv C))).card := by
  classical
  set t := hammingDisagreement (β.patch * A.act s) (A.act s * β.patch) with ht
  have hsplit := Finset.card_sdiff_add_card_inter t β.domain
  have hleft : (t \ β.domain).card ≤ (Finset.univ \ β.domain).card :=
    Finset.card_le_card
      (Finset.sdiff_subset_sdiff (Finset.subset_univ _) (Finset.Subset.refl _))
  have hfilter := Finset.card_filter_add_card_filter_not
    (s := t ∩ β.domain) (fun y ↦ A.act s y ∈ β.domain)
  -- the label moves the point off the glued domain
  have hmoved : ((t ∩ β.domain).filter fun y ↦ ¬ A.act s y ∈ β.domain).card ≤
      (Finset.univ \ β.domain).card := by
    refine Finset.card_le_card_of_injOn (A.act s) ?_ ?_
    · intro y hy
      rw [Finset.mem_filter] at hy
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, hy.2⟩
    · intro y _ z _ hyz
      exact (A.act s).injective hyz
  -- the label keeps the point in the glued domain
  have hkept : ((t ∩ β.domain).filter fun y ↦ A.act s y ∈ β.domain) ⊆
      (β.labelDefect A s).image β.domIncl := by
    intro y hy
    rw [Finset.mem_filter, Finset.mem_inter] at hy
    obtain ⟨⟨hyt, hyd⟩, hayd⟩ := hy
    obtain ⟨⟨C, x, hx⟩, rfl⟩ := β.mem_domain.mp hyd
    obtain ⟨⟨C', x', hx'⟩, hd'⟩ := β.mem_domain.mp hayd
    have hcompat : A.act s (E.embed C x) = E.embed C (A.blockAct C s x) :=
      (A.embed_blockAct C s x).symm
    have hd'' : E.embed C' x' = E.embed C (A.blockAct C s x) := hd'.trans hcompat
    have hCC : C' = C := E.embed_disjoint C' C x' (A.blockAct C s x) hd''
    subst hCC
    have hxx : x' = A.blockAct _ s x := E.embed_injective _ hd''
    subst hxx
    rw [Finset.mem_image]
    refine ⟨⟨_, x, hx⟩, ?_, rfl⟩
    rw [labelDefect, Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_attach _ _, ?_⟩
    rw [equivarianceDefect, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun hx₁ hsx₁ heq ↦ ?_⟩
    apply (mem_hammingDisagreement _ _ _).mp hyt
    change β.patch (A.act s (E.embed _ x)) = A.act s (β.patch (E.embed _ x))
    rw [hcompat, β.patch_embed _ _ hsx₁, β.patch_embed _ x hx₁]
    change E.embed _ ((β.arrow _).apply (A.blockAct _ s x) hsx₁) = _
    rw [heq, A.embed_blockAct]
  have hkeptCard : ((t ∩ β.domain).filter fun y ↦ A.act s y ∈ β.domain).card ≤
      (β.labelDefect A s).card :=
    (Finset.card_le_card hkept).trans Finset.card_image_le
  have hlabel := β.card_labelDefect_le A s
  omega

end BlockArrows
end BlockPatching
end GroupApproximation
