import GroupApproximation.KunThom.FixedPointNormalizationComparison

/-!
# Bridges between embedded blocks realized by a permutation

The relative cluster functor of Kun and Thom (arXiv:2608.06222, Lemma 4.3)
carries arrows through the overlap maps `m_{n,i}` of a compressor.  Such a map
is the restriction of the permutation `u_n` from a retained component to the
part of its image lying in the matched component.  This file builds that map
for an arbitrary `BlockEmbedding` and bounds its equivariance defect.

* `BlockEmbedding.bridge E q C D`: the partial bijection from block `C` to block
  `D` realized by the permutation `q`, with `embed_bridge_apply` and
  `realizesOn_bridge`.  The bridge is a reference arrow in the sense of
  `BlockArrows.RealizesOn`.
* `card_bridge_labelSlice_le` and `card_equivarianceDefect_bridge_le`: for block
  actions `A` on the source and `A'` on the target, the defect of the bridge is
  at most, for every label `s`, the missing source mass, the compatibility
  failures of both block actions, and the points where `q` fails to conjugate
  `A.act s` into `A'.act s`.
-/

namespace GroupApproximation
namespace BlockPatching
namespace BlockEmbedding

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

/-- The points of block `C` that the permutation `q` carries into block `D`. -/
noncomputable def bridgeSource (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    Finset (E.model C) := by
  classical
  exact Finset.univ.filter fun x ↦ ∃ z : E.model D, E.embed D z = q (E.embed C x)

/-- The points of block `D` that `q⁻¹` carries into block `C`. -/
noncomputable def bridgeTarget (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    Finset (E.model D) := by
  classical
  exact Finset.univ.filter fun z ↦ ∃ x : E.model C, E.embed C x = q⁻¹ (E.embed D z)

theorem mem_bridgeSource (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (x : E.model C) :
    x ∈ E.bridgeSource q C D ↔ ∃ z : E.model D, E.embed D z = q (E.embed C x) := by
  classical
  simp [bridgeSource]

theorem mem_bridgeTarget (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (z : E.model D) :
    z ∈ E.bridgeTarget q C D ↔ ∃ x : E.model C, E.embed C x = q⁻¹ (E.embed D z) := by
  classical
  simp [bridgeTarget]

/-- The point of block `D` hit by a bridge source point. -/
noncomputable def bridgeApply (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (x : E.model C) (hx : x ∈ E.bridgeSource q C D) : E.model D :=
  Classical.choose ((E.mem_bridgeSource q C D x).mp hx)

theorem embed_bridgeApply (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (x : E.model C) (hx : x ∈ E.bridgeSource q C D) :
    E.embed D (E.bridgeApply q C D x hx) = q (E.embed C x) :=
  Classical.choose_spec ((E.mem_bridgeSource q C D x).mp hx)

/-- The point of block `C` hit by `q⁻¹` from a bridge target point. -/
noncomputable def bridgeApplyInv (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (z : E.model D) (hz : z ∈ E.bridgeTarget q C D) : E.model C :=
  Classical.choose ((E.mem_bridgeTarget q C D z).mp hz)

theorem embed_bridgeApplyInv (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (z : E.model D) (hz : z ∈ E.bridgeTarget q C D) :
    E.embed C (E.bridgeApplyInv q C D z hz) = q⁻¹ (E.embed D z) :=
  Classical.choose_spec ((E.mem_bridgeTarget q C D z).mp hz)

theorem bridgeApply_mem_target (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (x : E.model C) (hx : x ∈ E.bridgeSource q C D) :
    E.bridgeApply q C D x hx ∈ E.bridgeTarget q C D := by
  rw [mem_bridgeTarget]
  refine ⟨x, ?_⟩
  rw [E.embed_bridgeApply q C D x hx, Equiv.Perm.coe_inv, q.symm_apply_apply]

theorem bridgeApplyInv_mem_source (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (z : E.model D) (hz : z ∈ E.bridgeTarget q C D) :
    E.bridgeApplyInv q C D z hz ∈ E.bridgeSource q C D := by
  rw [mem_bridgeSource]
  refine ⟨z, ?_⟩
  rw [E.embed_bridgeApplyInv q C D z hz, Equiv.Perm.coe_inv, q.apply_symm_apply]

theorem bridgeApplyInv_bridgeApply (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (x : E.model C) (hx : x ∈ E.bridgeSource q C D) :
    E.bridgeApplyInv q C D (E.bridgeApply q C D x hx) (E.bridgeApply_mem_target q C D x hx) =
      x := by
  apply E.embed_injective C
  rw [E.embed_bridgeApplyInv, E.embed_bridgeApply, Equiv.Perm.coe_inv, q.symm_apply_apply]

theorem bridgeApply_bridgeApplyInv (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (z : E.model D) (hz : z ∈ E.bridgeTarget q C D) :
    E.bridgeApply q C D (E.bridgeApplyInv q C D z hz) (E.bridgeApplyInv_mem_source q C D z hz) =
      z := by
  apply E.embed_injective D
  rw [E.embed_bridgeApply, E.embed_bridgeApplyInv, Equiv.Perm.coe_inv, q.apply_symm_apply]

/-- The partial bijection from block `C` to block `D` realized by `q`. -/
noncomputable def bridge (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    FinitePartialBijection (E.model C) (E.model D) where
  source := E.bridgeSource q C D
  target := E.bridgeTarget q C D
  equiv :=
    { toFun := fun x ↦
        ⟨E.bridgeApply q C D x.1 x.2, E.bridgeApply_mem_target q C D x.1 x.2⟩
      invFun := fun z ↦
        ⟨E.bridgeApplyInv q C D z.1 z.2, E.bridgeApplyInv_mem_source q C D z.1 z.2⟩
      left_inv := fun x ↦ Subtype.ext (E.bridgeApplyInv_bridgeApply q C D x.1 x.2)
      right_inv := fun z ↦ Subtype.ext (E.bridgeApply_bridgeApplyInv q C D z.1 z.2) }

@[simp] theorem bridge_source (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) :
    (E.bridge q C D).source = E.bridgeSource q C D :=
  rfl

/-- The bridge is the permutation `q` read through the two embeddings. -/
theorem embed_bridge_apply (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I)
    (x : E.model C) (hx : x ∈ (E.bridge q C D).source) :
    E.embed D ((E.bridge q C D).apply x hx) = q (E.embed C x) :=
  E.embed_bridgeApply q C D x hx

/-- The bridge into the image block of a block permutation realizes `q` on its
source. -/
theorem realizesOn_bridge (β : BlockArrows E) (q : Equiv.Perm Y) (C : I) :
    β.RealizesOn q C (E.bridge q C (β.objEquiv C)) :=
  fun x hx ↦ E.embed_bridge_apply q C (β.objEquiv C) x hx

/-! ### Equivariance defect of a bridge -/

/-- A labelled set is at most the sum over labels of its label slices. -/
theorem card_le_sum_labelSlices {L : Type*} [Fintype L] [DecidableEq L] {X : FiniteModel}
    (S : Finset (L × X)) :
    S.card ≤ ∑ s : L, (Finset.univ.filter fun x : X ↦ (s, x) ∈ S).card := by
  have hsub : S ⊆ Finset.univ.biUnion fun s : L ↦
      (Finset.univ.filter fun x : X ↦ (s, x) ∈ S).image fun x ↦ (s, x) := by
    intro p hp
    rw [Finset.mem_biUnion]
    exact ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr
      ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩⟩
  calc S.card
      ≤ (Finset.univ.biUnion fun s : L ↦
          (Finset.univ.filter fun x : X ↦ (s, x) ∈ S).image fun x ↦ (s, x)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ s : L, ((Finset.univ.filter fun x : X ↦ (s, x) ∈ S).image fun x ↦ (s, x)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ s : L, (Finset.univ.filter fun x : X ↦ (s, x) ∈ S).card :=
        Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le

/-- **One label.**  The defect of the bridge at label `s` is at most its missing
source mass, the compatibility failures of both block actions at `s`, and the
ambient points where `q` fails to conjugate `A.act s` into `A'.act s`. -/
theorem card_bridge_labelSlice_le {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) (A A' : BlockAction E L) (s : L) :
    (Finset.univ.filter fun x : E.model C ↦
        (s, x) ∈ (E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)).card ≤
      (E.bridge q C D).sourceDefect + (A.compatFailure C s).card +
        (Finset.univ.filter fun y : Y ↦ q (A.act s y) ≠ A'.act s (q y)).card +
          (A'.compatFailure D s).card := by
  have hsub : (Finset.univ.filter fun x : E.model C ↦
        (s, x) ∈ (E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)) ⊆
      ((Finset.univ \ (E.bridge q C D).source) ∪ A.compatFailure C s) ∪
        (Finset.univ.filter fun x : E.model C ↦
          q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))) ∪
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
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h₂⟩))
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
      (Finset.univ.filter fun x : E.model C ↦
        q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))))
    (Finset.univ.filter fun x : E.model C ↦
      q (E.embed C x) ∈ (A'.compatFailure D s).image (E.embed D))
  have hu₂ := Finset.card_union_le
    ((Finset.univ \ (E.bridge q C D).source) ∪ A.compatFailure C s)
    (Finset.univ.filter fun x : E.model C ↦
      q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x)))
  have hu₃ := Finset.card_union_le (Finset.univ \ (E.bridge q C D).source)
    (A.compatFailure C s)
  have hsd : (Finset.univ \ (E.bridge q C D).source).card ≤ (E.bridge q C D).sourceDefect := by
    have hsplit := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (E.bridge q C D).source)
    rw [Finset.card_univ] at hsplit
    unfold FinitePartialBijection.sourceDefect
    omega
  have hconj : (Finset.univ.filter fun x : E.model C ↦
        q (A.act s (E.embed C x)) ≠ A'.act s (q (E.embed C x))).card ≤
      (Finset.univ.filter fun y : Y ↦ q (A.act s y) ≠ A'.act s (q y)).card := by
    apply Finset.card_le_card_of_injOn (E.embed C)
    · intro x hx
      rw [Finset.mem_coe] at hx ⊢
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    · intro x _ x' _ hxx'
      exact E.embed_injective C hxx'
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

/-- **Bridge defect.**  The equivariance defect of a bridge is at most, summed
over labels, its missing source mass, the compatibility failures of both block
actions, and the conjugation failures of `q`. -/
theorem card_equivarianceDefect_bridge_le {L : Type*} [Fintype L] [DecidableEq L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C D : I) (A A' : BlockAction E L) :
    ((E.bridge q C D).equivarianceDefect (A.blockAct C) (A'.blockAct D)).card ≤
      ∑ s : L, ((E.bridge q C D).sourceDefect + (A.compatFailure C s).card +
        (Finset.univ.filter fun y : Y ↦ q (A.act s y) ≠ A'.act s (q y)).card +
          (A'.compatFailure D s).card) :=
  (card_le_sum_labelSlices _).trans
    (Finset.sum_le_sum fun s _ ↦ card_bridge_labelSlice_le E q C D A A' s)

end BlockEmbedding
end BlockPatching
end GroupApproximation
