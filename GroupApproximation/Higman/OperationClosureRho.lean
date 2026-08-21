import GroupApproximation.Higman.Operations

/-!
# Higman's operation `ρ`, and the single statement it reduces to

`ρ B = {f | ∃ g ∈ B, ∀ i, f i = g (-i)}` --- reflect the index.  This file
carries the reflection all the way through the coding and reduces the closure
of benignness under `ρ` to one statement in which no ordering appears at all.

`Higman.ShiftOperation` closes `σ` because `i ↦ i + 1` is order-preserving, so
it commutes with the sort that defines `elt`, and the shift is therefore
induced by an automorphism of `F₃`.  The reflection `i ↦ -i` is
order-*reversing*, and the trap recorded in
`notes/HIGMAN_EMBEDDING_FORMALIZATION_PLAN.md` is real: the sorted support
comes out backwards.  What is proved here is that the backwardness is *all*
that happens, and that it is exactly one inversion:

    elt (rhoSeq f) = (rhoFree (elt f))⁻¹                    (`elt_rhoSeq`)
    bElt (rhoSeq f) = (rhoAut (bElt f))⁻¹                   (`bElt_rhoSeq`)
    aElt (rhoSeq f) = rhoAut (bElt f * a * (bElt f)⁻¹)      (`aElt_rhoSeq`)

with `rhoAut : a ↦ a, b ↦ b⁻¹, c ↦ c⁻¹` an automorphism of `F₃`.  The
conjugator is inverted, and `aElt` conjugates `a` the other way round; so the
subgroup attached to `ρ B` is the automorphic image not of `A_B` but of

    barASub B = ⟨ b_f a b_f⁻¹ : f ∈ B ⟩,

the same generators with the conjugators inverted (`ASub_rhoOp`).  Since
benignness is preserved by automorphisms of the ambient group, this leaves
exactly one thing to prove:

> **if `A_B` is benign then so is `barASub B`.**

That statement has no sort, no support and no sequence space in it --- it is
the assertion that inverting the conjugators of a benign group of `a`-conjugates
keeps it benign --- and `benignTF_ASub_rhoOp` is the proof that nothing else
stands between it and Higman's `ρ`.

## How the remaining statement is meant to be proved

Section 6 states it in the ambient-free form it is really about
(`conjSub`, `conjSubInv`) and reduces it further, to a group-theoretic
*construction* plus the torsion-free form of the image half of Higman's Lemma
3.3.  Both are collected in `FlipWitness`, and `benignTF_conjSubInv` is the
proof that a `FlipWitness` closes `ρ`.

The construction asked for is this.  The normal closure `N` of `a` in `F₃` is
free on `{a^w : w ∈ K}` (`Conj.cbHom_injective`), and `K` acts on that basis by
*right* translation, `w ↦ w k`.  Inverting the basis index, `a^w ↦ a^{w⁻¹}`,
is an automorphism of `N` --- it permutes a free basis --- but it does *not*
extend to `F₃`, because it turns right translations into left translations.
It does extend to

    G = N ⋊ (K × K) = F₃ ⋊_ψ K,   ψ_k : a ↦ a^k, b ↦ b, c ↦ c,

where the second copy of `K` acts by left translation.  Each `ψ_k` is a
partial conjugation, hence an automorphism of `F₃`, so `G` is *two* HNN
extensions over `F₃` --- finitely presented by
`HNNFinitePresentation.isFinitelyPresented_hnnExtension` and torsion-free by
`HNNBritton.isPowerTorsionFree_hnn`.  Its finite presentation is

    ⟨a, b, c, β, γ | [β, b], [β, c], [γ, b], [γ, c], [a, bβ], [a, cγ]⟩

and the flip is the automorphism of `G` fixing `a` and exchanging the two
copies of `K`, `b ↔ β` and `c ↔ γ`; it sends `a^w` to `a^{w⁻¹}` for every
`w ∈ K`, which is the field `flip_conj`.

Note that the flip is asked for as an *automorphism* rather than as an
element: `benignTF_of_aut` needs only that the ambient group has an
automorphism doing the job, because `BenignTF.congr` accepts any isomorphism.
That is what removes the third HNN stage a stable letter would have cost.

The other field, `transport`, is the torsion-free form of the image half of
Higman's Lemma 3.3.  `Higman.BenignWitness.mapEmb` proves it without the
torsion clause, by the amalgam `K *_{F₃} G` of the benign witness with the new
ambient group; the clause it does not carry is that an amalgamated free
product of torsion-free groups is torsion-free, which
`Higman.BenignTorsionFree` deliberately avoided ever needing.

There is a second route to `transport` which needs no amalgam theorem at all,
and the group above was chosen so that it is available.  When `G` is a tower
of HNN extensions over `F₃` whose associated subgroups are finitely generated
subgroups of the stage below, the amalgam `K *_{F₃} G` *is* the same tower
built over `K` instead of over `F₃` --- the associated subgroups and the
identifying isomorphisms all live inside `F₃ ≤ K` --- so its finite
presentation is `HNNFinitePresentation.isFinitelyPresented_hnnExtension` and
its torsion clause is `HNNBritton.isPowerTorsionFree_hnn`, both already
proved here.  What that route costs instead is one Britton computation, that
`G` meets `K` inside the tower in exactly `F₃`.
-/

namespace GroupApproximation
namespace Higman
namespace Seq

open GroupApproximation.Higman.Conj

/-! ## 1.  Sorting against an order-reversing bijection -/

/-- Negation, as a permutation of the index set. -/
def negEquiv : ℤ ≃ ℤ where
  toFun i := -i
  invFun i := -i
  left_inv := neg_neg
  right_inv := neg_neg

@[simp] theorem negEquiv_apply (i : ℤ) : negEquiv i = -i := rfl

@[simp] theorem negEquiv_symm_apply (i : ℤ) : negEquiv.symm i = -i := rfl

/-- **Sorting against negation reverses the list.**  This is the whole of the
difference between `ρ` and `σ`: `Finset.map_sort` transports a sort along an
order-preserving embedding, and negation is order-reversing, so what comes out
is the reverse of the transported list.  Uniqueness of a sorted list among the
permutations of its multiset is Mathlib's
`List.Perm.eq_reverse_of_sortedLE_of_sortedGE`. -/
theorem sort_map_neg (s : Finset ℤ) :
    (s.map negEquiv.toEmbedding).sort (· ≤ ·)
      = ((s.sort (· ≤ ·)).map (fun i : ℤ => -i)).reverse := by
  refine List.Perm.eq_reverse_of_sortedLE_of_sortedGE ?_ ?_ ?_
  · rw [← Multiset.coe_eq_coe]
    have hcoe : ((List.map (fun x : ℤ => -x) (s.sort (· ≤ ·)) : List ℤ) : Multiset ℤ)
        = Multiset.map (fun x : ℤ => -x) ((s.sort (· ≤ ·) : List ℤ) : Multiset ℤ) := rfl
    rw [hcoe, Finset.sort_eq]
    simp
  · exact List.Pairwise.sortedLE (Finset.pairwise_sort _ _)
  · refine List.Pairwise.sortedGE ?_
    rw [List.pairwise_map]
    exact (Finset.pairwise_sort s (· ≤ ·)).imp fun hab => neg_le_neg hab

/-! ## 2.  The reflection on sequences -/

/-- The reflection of a sequence. -/
noncomputable def rhoSeq (f : E) : E := Finsupp.equivMapDomain negEquiv f

@[simp] theorem rhoSeq_apply (f : E) (i : ℤ) : rhoSeq f i = f (-i) := by
  unfold rhoSeq
  rw [Finsupp.equivMapDomain_apply]
  rfl

theorem rhoSeq_support (f : E) :
    (rhoSeq f).support = f.support.map negEquiv.toEmbedding := rfl

/-- The reflection on the free group of the index set.  The generator goes to
the *inverse* of the reflected generator: that is what makes `elt_rhoSeq` an
identity rather than an identity up to an inversion inside the product. -/
def rhoFree : FreeGroup ℤ →* FreeGroup ℤ :=
  FreeGroup.lift (fun i : ℤ => (FreeGroup.of (-i))⁻¹)

@[simp] theorem rhoFree_of (i : ℤ) :
    rhoFree (FreeGroup.of i) = (FreeGroup.of (-i))⁻¹ := by
  unfold rhoFree
  rw [FreeGroup.lift_apply_of]

/-- **The coding intertwines the reflection with one inversion.** -/
theorem elt_rhoSeq (f : E) : elt (rhoSeq f) = (rhoFree (elt f))⁻¹ := by
  unfold elt
  rw [rhoSeq_support, sort_map_neg, List.map_reverse, List.prod_reverse_noncomm,
    List.map_map, List.map_map, map_list_prod, List.map_map]
  refine congrArg (fun x : FreeGroup ℤ => x⁻¹) (congrArg List.prod ?_)
  refine List.map_congr_left fun j _ => ?_
  show (FreeGroup.of (-j) ^ rhoSeq f (-j))⁻¹ = rhoFree (FreeGroup.of j ^ f j)
  rw [map_zpow, rhoFree_of, rhoSeq_apply, neg_neg, inv_zpow]

/-! ## 3.  The automorphism of `F₃` -/

/-- The automorphism realizing the reflection. -/
def rhoAut : F₃ →* F₃ :=
  FreeGroup.lift (fun i : Fin 3 => if i = 0 then a else if i = 1 then b⁻¹ else c⁻¹)

@[simp] theorem rhoAut_a : rhoAut a = a := by
  unfold rhoAut a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem rhoAut_b : rhoAut b = b⁻¹ := by
  unfold rhoAut b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem rhoAut_c : rhoAut c = c⁻¹ := by
  unfold rhoAut c
  rw [FreeGroup.lift_apply_of]
  simp

theorem rhoAut_comp_rhoAut : rhoAut.comp rhoAut = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · show rhoAut (rhoAut a) = a
    rw [rhoAut_a, rhoAut_a]
  · show rhoAut (rhoAut b) = b
    rw [rhoAut_b, map_inv, rhoAut_b, inv_inv]
  · show rhoAut (rhoAut c) = c
    rw [rhoAut_c, map_inv, rhoAut_c, inv_inv]

/-- The reflection, as an automorphism of `F₃`.  It is an involution. -/
def rhoEquiv : F₃ ≃* F₃ where
  toFun := rhoAut
  invFun := rhoAut
  left_inv x := congrArg (fun f : F₃ →* F₃ => f x) rhoAut_comp_rhoAut
  right_inv x := congrArg (fun f : F₃ →* F₃ => f x) rhoAut_comp_rhoAut
  map_mul' := map_mul _

@[simp] theorem rhoEquiv_toMonoidHom : rhoEquiv.toMonoidHom = rhoAut := rfl

@[simp] theorem rhoEquiv_symm : rhoEquiv.symm = rhoEquiv := rfl

/-- **The automorphism reflects the rows, and inverts them.** -/
theorem rhoAut_rowElt (i : ℤ) : rhoAut (rowElt i) = (rowElt (-i))⁻¹ := by
  unfold rowElt
  rw [map_mul, map_mul, map_zpow, map_zpow, rhoAut_b, rhoAut_c, neg_neg]
  simp only [inv_zpow]
  group

theorem rhoAut_comp_rowHom : rhoAut.comp rowHom = rowHom.comp rhoFree := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  show rhoAut (rowHom (FreeGroup.of i)) = rowHom (rhoFree (FreeGroup.of i))
  rw [rowHom_of, rhoFree_of, map_inv, rowHom_of, rhoAut_rowElt]

/-! ## 4.  The reflection on the coding -/

theorem bElt_rhoSeq (f : E) : bElt (rhoSeq f) = (rhoAut (bElt f))⁻¹ := by
  unfold bElt
  rw [elt_rhoSeq, map_inv]
  refine congrArg (fun x : F₃ => x⁻¹) ?_
  exact (congrArg (fun g : FreeGroup ℤ →* F₃ => g (elt f)) rhoAut_comp_rowHom).symm

/-- The conjugate attached to a sequence, with the conjugator inverted. -/
noncomputable def barElt (f : E) : F₃ := bElt f * a * (bElt f)⁻¹

/-- The subgroup attached to a set of sequences, with the conjugators
inverted. -/
noncomputable def barASub (B : Set E) : Subgroup F₃ :=
  Subgroup.closure (barElt '' B)

/-- **The reflection carries the inverted coding to the ordinary one.** -/
theorem aElt_rhoSeq (f : E) : aElt (rhoSeq f) = rhoAut (barElt f) := by
  unfold aElt barElt
  rw [bElt_rhoSeq, inv_inv, map_mul, map_mul, rhoAut_a, map_inv]

/-! ## 5.  The operation -/

theorem rhoOp_eq_image (B : Set E) : rhoOp B = rhoSeq '' B := by
  refine Set.ext fun f => ?_
  constructor
  · rintro ⟨g, hg, hfg⟩
    refine ⟨g, hg, Finsupp.ext fun i => ?_⟩
    rw [rhoSeq_apply]
    exact (hfg i).symm
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, fun i => rhoSeq_apply g i⟩

/-- **The subgroup of a reflected set is the automorphic image of the inverted
subgroup.** -/
theorem ASub_rhoOp (B : Set E) : ASub (rhoOp B) = (barASub B).map rhoAut := by
  unfold ASub barASub
  rw [MonoidHom.map_closure]
  congr 1
  refine Set.ext fun x => ?_
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [rhoOp_eq_image] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact ⟨barElt g, ⟨g, hg, rfl⟩, (aElt_rhoSeq g).symm⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨rhoSeq g, ?_, aElt_rhoSeq g⟩
    rw [rhoOp_eq_image]
    exact ⟨g, hg, rfl⟩

/-- **Higman's operation `ρ`, modulo the inverted coding.**  Everything that
the reflection does to the sort is discharged here; what is left is a
statement about conjugators alone. -/
theorem benignTF_ASub_rhoOp {B : Set E} (h : BenignTF (barASub B)) :
    BenignTF (ASub (rhoOp B)) := by
  have hmap : ASub (rhoOp B) = (barASub B).comap (rhoEquiv.symm).toMonoidHom := by
    rw [ASub_rhoOp, ← rhoEquiv_toMonoidHom]
    exact Subgroup.map_equiv_eq_comap_symm' rhoEquiv (barASub B)
  rw [hmap]
  exact BenignTF.congr rhoEquiv.symm h

/-! ## 6.  The statement that is left, and what proves it -/

/-- The subgroup generated by the conjugates `a ^ h`, `h` running through a set
of conjugators. -/
noncomputable def conjSub (T : Set F₃) : Subgroup F₃ :=
  Subgroup.closure ((fun h : F₃ => h⁻¹ * a * h) '' T)

/-- The same, with the conjugators inverted. -/
noncomputable def conjSubInv (T : Set F₃) : Subgroup F₃ :=
  Subgroup.closure ((fun h : F₃ => h * a * h⁻¹) '' T)

theorem ASub_eq_conjSub (B : Set E) : ASub B = conjSub (bElt '' B) := by
  unfold ASub conjSub
  rw [Set.image_image]
  rfl

theorem barASub_eq_conjSubInv (B : Set E) : barASub B = conjSubInv (bElt '' B) := by
  unfold barASub conjSubInv
  rw [Set.image_image]
  rfl

/-- `F₃` is its own torsion-free finitely presented overgroup. -/
def f3Overgroup : TorsionFreeFPOvergroup F₃ where
  K := F₃
  torsionFree := IsPowerTorsionFree.of_isMulTorsionFree
  emb := MonoidHom.id F₃
  emb_injective := fun _ _ h => h

/-- **Input: a group in which the conjugators can be inverted.**

The two fields that are not bookkeeping are `flip_conj` --- an element of a
finitely presented torsion-free overgroup of `F₃` whose conjugation action
inverts the index of every basis element `a ^ h`, `h ∈ K`, of the normal
closure of `a` --- and `transport`, the torsion-free form of the image half of
Higman's Lemma 3.3 at that one embedding.  `Higman.BenignWitness.mapEmb`
proves `transport` without the torsion clause; the clause costs exactly the
statement that an amalgamated free product of torsion-free groups is
torsion-free, which is the one permanence theorem
`Higman.BenignTorsionFree` does not already have.

The header of this file gives the group and its finite presentation.

**Nothing inhabits this structure.** -/
structure FlipWitness where
  /-- The overgroup. -/
  G : Type
  /-- Its group structure. -/
  [group : Group G]
  /-- It is finitely presented. -/
  [fp : Group.IsFinitelyPresented G]
  /-- It is torsion-free. -/
  torsionFree : IsPowerTorsionFree G
  /-- `F₃` sits inside it. -/
  emb : F₃ →* G
  /-- ... as a subgroup. -/
  emb_injective : Function.Injective emb
  /-- The automorphism that inverts the conjugators. -/
  flip : G ≃* G
  /-- ... which does. -/
  flip_conj : ∀ h : F₃, h ∈ K → flip (emb (h⁻¹ * a * h)) = emb (h * a * h⁻¹)
  /-- Benignness with a torsion-free witness survives the enlargement of the
  ambient group. -/
  transport : ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb)

attribute [instance] FlipWitness.group FlipWitness.fp

/-- **Conjugation inside an enlarged ambient group transports benignness.**

If `F₃` embeds in a group in which benignness with a torsion-free witness
survives the enlargement, and if some element of that group conjugates the
image of `H` onto the image of `H'`, then `H'` is benign as soon as `H` is:
enlarge, conjugate --- which is an automorphism of the ambient group, so
`BenignTF.congr` applies --- and come back down by `BenignTF.comap`.

This is the shape every Higman operation that is not induced by an
endomorphism of `F₃` has: `ρ` below, and `τ` in
`Higman.OperationClosureTau`. -/
theorem benignTF_of_aut {G : Type} [Group G] (emb : F₃ →* G)
    (hemb : Function.Injective emb) (Φ : G ≃* G)
    (transport : ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb))
    {H H' : Subgroup F₃}
    (hconj : (H.map emb).map Φ.toMonoidHom = H'.map emb)
    (h : BenignTF H) : BenignTF H' := by
  have h₁ : BenignTF (H.map emb) := transport _ h
  have h₂ : BenignTF ((H.map emb).map Φ.toMonoidHom) := by
    have hc := BenignTF.congr Φ.symm h₁
    rwa [← Subgroup.map_equiv_eq_comap_symm'] at hc
  rw [hconj] at h₂
  have h₃ := BenignTF.comap f3Overgroup emb h₂
  rwa [Subgroup.comap_map_eq_self_of_injective hemb] at h₃

/-- The inner case, which is what `τ` uses. -/
theorem benignTF_of_conj {G : Type} [Group G] (emb : F₃ →* G)
    (hemb : Function.Injective emb) (t : G)
    (transport : ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb))
    {H H' : Subgroup F₃}
    (hconj : (H.map emb).map (MulAut.conj t).toMonoidHom = H'.map emb)
    (h : BenignTF H) : BenignTF H' :=
  benignTF_of_aut emb hemb (MulAut.conj t) transport hconj h

/-- **A flip inverts the conjugators of a benign group of `a`-conjugates.** -/
theorem benignTF_conjSubInv (w : FlipWitness) {T : Set F₃}
    (hT : T ⊆ (K : Set F₃)) (h : BenignTF (conjSub T)) :
    BenignTF (conjSubInv T) := by
  refine benignTF_of_aut w.emb w.emb_injective w.flip w.transport ?_ h
  unfold conjSub conjSubInv
  rw [MonoidHom.map_closure, MonoidHom.map_closure, MonoidHom.map_closure,
    Set.image_image, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x hx => ?_
  exact w.flip_conj x (hT hx)

/-- **Higman's operation `ρ`, from the flip.** -/
theorem benignTF_ASub_rhoOp_of_flip (w : FlipWitness) (B : Set E)
    (h : BenignTF (ASub B)) : BenignTF (ASub (rhoOp B)) := by
  refine benignTF_ASub_rhoOp ?_
  rw [barASub_eq_conjSubInv]
  refine benignTF_conjSubInv w ?_ ?_
  · rintro _ ⟨f, _, rfl⟩
    exact bElt_mem_K f
  · rw [← ASub_eq_conjSub]
    exact h

end Seq
end Higman
end GroupApproximation
