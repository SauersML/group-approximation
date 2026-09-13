import GroupApproximation.Sofic.OperatorMFLocalNormalization
import GroupApproximation.Meta.AxiomGuard

/-!
# Korchagin's Corollary 10 and Proposition 13

`non_mf_groups_exist.tex`, after `thm:amenable-trace` (origin/main, lines 272-274):

> Since `W_0` is a direct limit of residually finite groups, it is
> MF~\cite[Corollary~10 and Proposition~13]{Korchagin}.

and the remark after `prop:max-infinite` (lines 780-781):

> … so `V` is residually finite and MF~\cite[Corollary~10]{Korchagin}.

Korchagin (arXiv:1704.06906), §2:

* Corollary 10: "Residually MF-groups are MF-groups."
* Proposition 13: "Let `G_j` be MF-groups. Then `G = lim→ G_j` is also MF-group."

Both are proved here, with no literature input.

## Corollary 10

"Residually MF" is Korchagin's reading (proof of Proposition 6): every
nontrivial `g` survives some homomorphism to an MF group.  The proof is
Korchagin's block sum.  For a finite set `F` and a tolerance `ε`, each ordered
distinct pair `(r, s)` in `F` gives a homomorphism `φ` to an MF group with
`φ r ≠ φ s` (it does not kill `r⁻¹ s`).  An operator-norm model of that group
with separation `1` (`OperatorMFLocalNormalization.isNormApproximable_one`,
Korchagin's Proposition 7) is pulled back along `φ`, and the finite block sum of
these pullbacks is a model of `F` at separation `1`.

## Proposition 13

The manuscript applies Proposition 13 to `W_0` as the directed union of its
finitely generated subgroups (tex line 1566, "The group `W_0` is their directed
union"), i.e. to the direct limit along inclusions.  That is the case proved
here: a countable group covered by a directed family of MF subgroups is MF.  A
finite set lies in one member, whose local model extends by the identity off
that member.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMFSentences
namespace KorchaginDirectLimit

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ### Corollary 10 -/

/-- Korchagin's "residually MF" (proof of Proposition 6): every nontrivial
element survives a homomorphism to an MF group. -/
def IsResiduallyMF (G : Type) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 → ∃ (Q : Type) (_ : Group Q), IsOperatorMF Q ∧ ∃ φ : G →* Q, φ g ≠ 1

/-- **Korchagin's block sum.**  A residually MF group has operator-norm local
models with separation `1`. -/
theorem isNormApproximable_one_of_isResiduallyMF {G : Type} [Group G]
    (hG : IsResiduallyMF G) : IsNormApproximable G 1 := by
  classical
  intro F ε hε
  let pairs : Finset (G × G) := (F ×ˢ F).filter fun q ↦ q.1 ≠ q.2
  let Pair : Type := {q : G × G // q ∈ pairs}
  have hpair (q : Pair) : q.1.1 ∈ F ∧ q.1.2 ∈ F ∧ q.1.1 ≠ q.1.2 := by
    have hq := q.2
    simp only [pairs, Finset.mem_filter, Finset.mem_product] at hq
    exact ⟨hq.1.1, hq.1.2, hq.2⟩
  have hsep (q : Pair) : ∃ (Q : Type) (_ : Group Q), IsOperatorMF Q ∧
      ∃ φ : G →* Q, φ q.1.1 ≠ φ q.1.2 := by
    obtain ⟨Q, _, hQ, φ, hφ⟩ := hG (q.1.1⁻¹ * q.1.2) fun h1 ↦
      (hpair q).2.2 (inv_mul_eq_one.mp h1)
    refine ⟨Q, inferInstance, hQ, φ, fun heq ↦ hφ ?_⟩
    rw [map_mul, map_inv, heq, inv_mul_cancel]
  choose Q hQgrp hQMF φ hφ using hsep
  have hblock (q : Pair) : ∃ B : UnitaryBlock G, 0 < Fintype.card B.model ∧
      (∀ r ∈ F, ∀ s ∈ F,
        ‖(B.map (r * s) : Matrix B.model B.model ℂ) -
          (B.map r : Matrix B.model B.model ℂ) *
            (B.map s : Matrix B.model B.model ℂ)‖ ≤ ε) ∧
      1 ≤ ‖(B.map q.1.1 : Matrix B.model B.model ℂ) - B.map q.1.2‖ := by
    letI := hQgrp q
    obtain ⟨M⟩ :=
      OperatorMFLocalNormalization.isNormApproximable_one (hQMF q) (F.image (φ q)) ε hε
    refine ⟨{ model := M.carrier
              map := fun x ↦ ⟨M.map (φ q x), M.isUnitary (φ q x)⟩ },
      M.nonempty, ?_, ?_⟩
    · intro r hr s hs
      show ‖M.map (φ q (r * s)) - M.map (φ q r) * M.map (φ q s)‖ ≤ ε
      rw [map_mul]
      exact M.multiplicative _ (Finset.mem_image_of_mem _ hr) _
        (Finset.mem_image_of_mem _ hs)
    · show 1 ≤ ‖M.map (φ q q.1.1) - M.map (φ q q.1.2)‖
      exact M.separated _ (Finset.mem_image_of_mem _ (hpair q).1) _
        (Finset.mem_image_of_mem _ (hpair q).2.1) (hφ q)
  choose B hBpos hBmul hBsep using hblock
  let trivial : UnitaryBlock G := {
    model := ⟨PUnit, inferInstance, inferInstance⟩
    map := fun _ ↦ 1 }
  let blocks : List (UnitaryBlock G) :=
    trivial :: (Finset.univ : Finset Pair).toList.map B
  refine ⟨{
    carrier := blockListModel blocks
    nonempty := card_blockListModel_pos_of_mem
      (show trivial ∈ blocks by simp [blocks]) (by simp [trivial])
    map := blockListMap blocks
    isUnitary := blockListMap_mem_unitaryGroup blocks
    multiplicative := ?_
    separated := ?_ }⟩
  · intro r hr s hs
    apply norm_blockListMap_mul_sub_le G blocks r s hε.le
    intro C hC
    rw [show blocks = trivial ::
        (Finset.univ : Finset Pair).toList.map B by rfl] at hC
    rcases List.mem_cons.mp hC with rfl | hC
    · simpa [trivial] using hε.le
    · rw [List.mem_map] at hC
      obtain ⟨q, _hq, rfl⟩ := hC
      exact hBmul q r hr s hs
  · intro r hr s hs hrs
    have hqmem : (r, s) ∈ pairs := by simp [pairs, hr, hs, hrs]
    let q : Pair := ⟨(r, s), hqmem⟩
    have hmem : B q ∈ blocks := by
      apply List.mem_cons_of_mem
      rw [List.mem_map]
      exact ⟨q, by simp, rfl⟩
    exact (hBsep q).trans (norm_blockListMap_sub_ge_of_mem hmem r s)

/-- **Corollary 10**, as printed: "Residually MF-groups are MF-groups."
Korchagin works with countable groups throughout (§2, "We will consider only
countable groups"). -/
def KorchaginCorollaryTen : Prop :=
  ∀ (G : Type) [Group G] [Countable G], IsResiduallyMF G → IsOperatorMF G

theorem korchaginCorollaryTen : KorchaginCorollaryTen := by
  intro G _ _ hG
  exact OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr
    (isNormApproximable_one_of_isResiduallyMF hG)

/-- A residually finite group is residually MF: finite quotients are MF. -/
theorem isResiduallyMF_of_residuallyFinite {G : Type} [Group G]
    [Group.ResiduallyFinite G] : IsResiduallyMF G := by
  intro g hg
  obtain ⟨H, hH⟩ := Group.exists_finiteIndexNormalSubgroup_notMem g hg
  refine ⟨G ⧸ H.toSubgroup, inferInstance, isOperatorMF_of_finite_standard _,
    QuotientGroup.mk' H.toSubgroup, ?_⟩
  rw [ne_eq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    FiniteIndexNormalSubgroup.mem_toSubgroup_iff]
  exact hH

/-- Countable residually finite groups are MF, through Corollary 10. -/
theorem isOperatorMF_of_residuallyFinite_viaCorollaryTen {G : Type} [Group G]
    [Countable G] [Group.ResiduallyFinite G] : IsOperatorMF G :=
  korchaginCorollaryTen G isResiduallyMF_of_residuallyFinite

/-! ### Proposition 13 -/

open Classical in
/-- A map on a subgroup, extended by the identity off it. -/
def extendOffSubgroup {G : Type} [Group G] (H : Subgroup G) {Y : FiniteModel}
    (m : H → Matrix Y Y ℂ) (g : G) : Matrix Y Y ℂ :=
  if hg : g ∈ H then m ⟨g, hg⟩ else 1

theorem extendOffSubgroup_of_mem {G : Type} [Group G] (H : Subgroup G)
    {Y : FiniteModel} (m : H → Matrix Y Y ℂ) {g : G} (hg : g ∈ H) :
    extendOffSubgroup H m g = m ⟨g, hg⟩ := by
  unfold extendOffSubgroup
  exact dif_pos hg

theorem extendOffSubgroup_mem_unitaryGroup {G : Type} [Group G] (H : Subgroup G)
    {Y : FiniteModel} (m : H → Matrix Y Y ℂ)
    (hm : ∀ x, m x ∈ Matrix.unitaryGroup Y ℂ) (g : G) :
    extendOffSubgroup H m g ∈ Matrix.unitaryGroup Y ℂ := by
  unfold extendOffSubgroup
  split_ifs
  · exact hm _
  · exact one_mem _

/-- **A directed union of MF subgroups is MF**: the local models of the member
containing a finite set, extended by the identity. -/
theorem isNormApproximable_one_of_directed {G : Type} [Group G] {ι : Type}
    (H : ι → Subgroup G) (hdir : Directed (· ≤ ·) H)
    (hcover : ∀ g : G, ∃ i, g ∈ H i) (hMF : ∀ i, IsOperatorMF (H i)) :
    IsNormApproximable G 1 := by
  classical
  intro F ε hε
  obtain ⟨i0, -⟩ := hcover 1
  haveI : Nonempty ι := ⟨i0⟩
  choose idx hidx using hcover
  obtain ⟨z, hz⟩ := hdir.finset_le (F.image idx)
  have hsub : ∀ g ∈ F, g ∈ H z := fun g hg ↦
    hz (idx g) (Finset.mem_image_of_mem idx hg) (hidx g)
  obtain ⟨M⟩ := OperatorMFLocalNormalization.isNormApproximable_one (hMF z)
    (F.subtype (· ∈ H z)) ε hε
  refine ⟨{
    carrier := M.carrier
    nonempty := M.nonempty
    map := extendOffSubgroup (H z) M.map
    isUnitary := extendOffSubgroup_mem_unitaryGroup (H z) M.map M.isUnitary
    multiplicative := ?_
    separated := ?_ }⟩
  · intro g hg h hh
    have hg' := hsub g hg
    have hh' := hsub h hh
    rw [extendOffSubgroup_of_mem (H z) M.map (mul_mem hg' hh'),
      extendOffSubgroup_of_mem (H z) M.map hg', extendOffSubgroup_of_mem (H z) M.map hh']
    exact M.multiplicative ⟨g, hg'⟩ (Finset.mem_subtype.mpr hg) ⟨h, hh'⟩
      (Finset.mem_subtype.mpr hh)
  · intro g hg h hh hne
    have hg' := hsub g hg
    have hh' := hsub h hh
    rw [extendOffSubgroup_of_mem (H z) M.map hg', extendOffSubgroup_of_mem (H z) M.map hh']
    exact M.separated ⟨g, hg'⟩ (Finset.mem_subtype.mpr hg) ⟨h, hh'⟩
      (Finset.mem_subtype.mpr hh) fun heq ↦ hne (congrArg Subtype.val heq)

/-- **Proposition 13**, for the direct limit along inclusions that the
manuscript uses: a countable group that is the directed union of MF subgroups
is MF. -/
def KorchaginPropositionThirteenForUnions : Prop :=
  ∀ (G : Type) [Group G] [Countable G] (ι : Type) (H : ι → Subgroup G),
    Directed (· ≤ ·) H → (∀ g : G, ∃ i, g ∈ H i) → (∀ i, IsOperatorMF (H i)) →
      IsOperatorMF G

theorem korchaginPropositionThirteenForUnions : KorchaginPropositionThirteenForUnions := by
  intro G _ _ ι H hdir hcover hMF
  exact OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one.mpr
    (isNormApproximable_one_of_directed H hdir hcover hMF)

/-! ### Finitely generated subgroups as a directed system -/

/-- The finitely generated subgroups form a directed family. -/
theorem directed_fgSubgroups (G : Type) [Group G] :
    Directed (· ≤ ·) (fun H : {H : Subgroup G // H.FG} ↦ H.1) := by
  intro a b
  exact ⟨⟨a.1 ⊔ b.1, a.2.sup b.2⟩, le_sup_left, le_sup_right⟩

/-- Every element lies in a finitely generated subgroup. -/
theorem exists_fgSubgroup_mem {G : Type} [Group G] (g : G) :
    ∃ H : {H : Subgroup G // H.FG}, g ∈ H.1 :=
  ⟨⟨Subgroup.closure {g}, ⟨{g}, by simp⟩⟩, Subgroup.subset_closure (Set.mem_singleton g)⟩

/-- A countable group whose finitely generated subgroups are residually finite
is MF: it is the directed union of residually finite, hence MF (Corollary 10),
subgroups (Proposition 13). -/
theorem isOperatorMF_of_forall_fg_residuallyFinite {G : Type} [Group G] [Countable G]
    (hG : ∀ H : Subgroup G, H.FG → Group.ResiduallyFinite H) : IsOperatorMF G :=
  korchaginPropositionThirteenForUnions G {H : Subgroup G // H.FG} (fun H ↦ H.1)
    (directed_fgSubgroups G) exists_fgSubgroup_mem fun H ↦ by
      haveI := hG H.1 H.2
      exact isOperatorMF_of_residuallyFinite_viaCorollaryTen

end

end KorchaginDirectLimit
end NonMFSentences
end Manuscript
end GroupApproximation

open GroupApproximation.Manuscript.NonMFSentences.KorchaginDirectLimit

#audit_axioms isNormApproximable_one_of_isResiduallyMF
#audit_axioms isResiduallyMF_of_residuallyFinite
#audit_axioms isNormApproximable_one_of_directed
#audit_axioms isOperatorMF_of_forall_fg_residuallyFinite
#audit_closed_axioms korchaginCorollaryTen
#audit_closed_axioms korchaginPropositionThirteenForUnions
