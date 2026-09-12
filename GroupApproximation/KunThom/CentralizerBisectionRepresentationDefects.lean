import GroupApproximation.KunThom.ComponentCountingRelativeFunctorRealization
import GroupApproximation.Matching.PartialClusterCandidates

/-!
# Local defects of the bridges of an almost-centralizer

Kun and Thom (arXiv:2608.06222v3, Lemma 4.2(4)) represent an element of the
centralizer of `σ(Γ)` by a patched bisection of the cluster groupoid.  In the
sequential setting the element is a permutation `q` of the ambient model that
almost commutes with the labels.  On a block `C` the natural arrow into a block
`D` is the bridge `BlockEmbedding.bridge E q C D`, the restriction of `q`.

The bound `BlockEmbedding.card_equivarianceDefect_bridge_le` counts the
commutation failures of `q` over the whole model once for every block, so it
does not sum over blocks.  This file charges every failure to the block where it
sits.

* `BlockAction.localObstruction A q C s`: the points of block `C` at which `q`
  fails to commute with the label `s`, the block action disagrees with the
  ambient action, or the image under `q` meets such a disagreement.
  `sum_card_localObstruction_le` sums them over all blocks.
* `card_equivarianceDefect_le_localObstruction`, with the bridge forms
  `card_equivarianceDefect_bridge_le_localObstruction` and
  `card_symm_equivarianceDefect_bridge_le_localObstruction`: the forward and
  backward defects of a bridge are its missing source or target mass, once per
  label, plus the local obstructions of `q` or `q⁻¹`.
* `card_taggedBoundary_source_le`: the source of a bridge is almost invariant.
  `sourceDefect_bridge_le_of_reseparation` and
  `targetDefect_bridge_le_of_reseparation` bound its missing mass through tagged
  expansion at a vanishing scale.
* `eq_of_isClusterCandidate_bridge` and `eq_of_isClusterCandidate_bridge_target`:
  a block has at most one candidate bridge out of it, and at most one into it.
* `mul_scale_le_of_not_isClusterCandidate`: a partial bijection that misses the
  candidate thresholds carries large defects at the cluster scale.
-/

namespace GroupApproximation
namespace BlockPatching

open FinitePartialBijection

universe u

variable {Y : FiniteModel} {I : Type u}

/-! ### Disjoint co-large partial bijections -/

/-- Two partial bijections out of one model with disjoint sources miss, together, at
least the whole model. -/
theorem card_le_sourceDefect_add_of_disjoint {X Z Z' : FiniteModel}
    (f : FinitePartialBijection X Z) (g : FinitePartialBijection X Z')
    (hfg : Disjoint f.source g.source) :
    Fintype.card X ≤ f.sourceDefect + g.sourceDefect := by
  have hunion := Finset.card_union_of_disjoint hfg
  have hle : (f.source ∪ g.source).card ≤ Fintype.card X := Finset.card_le_univ _
  unfold FinitePartialBijection.sourceDefect
  omega

/-- Two partial bijections into one model with disjoint targets miss, together, at
least the whole model. -/
theorem card_le_targetDefect_add_of_disjoint {X X' Z : FiniteModel}
    (f : FinitePartialBijection X Z) (g : FinitePartialBijection X' Z)
    (hfg : Disjoint f.target g.target) :
    Fintype.card Z ≤ f.targetDefect + g.targetDefect := by
  have hunion := Finset.card_union_of_disjoint hfg
  have hle : (f.target ∪ g.target).card ≤ Fintype.card Z := Finset.card_le_univ _
  unfold FinitePartialBijection.targetDefect
  omega

/-! ### Tagged expansion at a vanishing scale -/

/-- **Re-separation of a large set.**  If a set covering at least half of a model has
tagged boundary below `h` times the scale `⌊x⌋₊ + 1`, at which the model expands, then its
complement has at most `x` points. -/
theorem card_compl_le_of_taggedBoundary {L : Type*} [Fintype L] {X : FiniteModel}
    (act : L → Equiv.Perm X) {h x : ℝ} (hx : 0 ≤ x) (S : Finset X)
    (hexp : HasTaggedExpansionAtScale act h (⌊x⌋₊ + 1))
    (hbd : ((taggedBoundary act S).card : ℝ) < h * ((⌊x⌋₊ + 1 : ℕ) : ℝ))
    (hmaj : 2 * (Finset.univ \ S).card ≤ Fintype.card X) :
    ((Finset.univ \ S).card : ℝ) ≤ x := by
  have hlt : (Finset.univ \ S).card < ⌊x⌋₊ + 1 := by
    by_contra hge
    push Not at hge
    have hmain := hexp.2 (Finset.univ \ S) hge hmaj
    rw [taggedBoundary_compl] at hmain
    have hcast : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((Finset.univ \ S).card : ℝ) := by
      exact_mod_cast hge
    have hmul := mul_le_mul_of_nonneg_left hcast hexp.1.le
    linarith
  have hle : (Finset.univ \ S).card ≤ ⌊x⌋₊ := by omega
  calc ((Finset.univ \ S).card : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hle
    _ ≤ x := Nat.floor_le hx

/-! ### The candidate thresholds -/

/-- **Missing the candidate thresholds costs defects.**  A partial bijection that is not a
cluster candidate at scale `m` has `h * m` below its two defect masses at level `h` plus
twice its forward and backward equivariance defects. -/
theorem mul_scale_le_of_not_isClusterCandidate {L : Type*} [Fintype L] {X Z : FiniteModel}
    {actX : L → Equiv.Perm X} {actZ : L → Equiv.Perm Z} {h : ℝ} {m : ℕ} (hh : 0 ≤ h)
    {f : FinitePartialBijection X Z} (hf : ¬ f.IsClusterCandidate actX actZ h m) :
    h * m ≤ h * ((f.sourceDefect + f.targetDefect : ℕ) : ℝ) +
      2 * (((f.equivarianceDefect actX actZ).card : ℝ) +
        ((f.symm.equivarianceDefect actZ actX).card : ℝ)) := by
  have ha : (0 : ℝ) ≤ ((f.equivarianceDefect actX actZ).card : ℝ) := Nat.cast_nonneg _
  have hb : (0 : ℝ) ≤ ((f.symm.equivarianceDefect actZ actX).card : ℝ) := Nat.cast_nonneg _
  have hs : (0 : ℝ) ≤ h * ((f.sourceDefect + f.targetDefect : ℕ) : ℝ) :=
    mul_nonneg hh (Nat.cast_nonneg _)
  by_cases hself : f.sourceDefect + f.targetDefect < 2 * m
  · by_cases hfwd : ((f.equivarianceDefect actX actZ).card : ℝ) < h * m / 2
    · by_cases hbwd : ((f.symm.equivarianceDefect actZ actX).card : ℝ) < h * m / 2
      · exact (hf ⟨hself, hfwd, hbwd⟩).elim
      · push Not at hbwd
        linarith
    · push Not at hfwd
      linarith
  · push Not at hself
    have hcast : (2 * m : ℝ) ≤ ((f.sourceDefect + f.targetDefect : ℕ) : ℝ) := by
      exact_mod_cast hself
    have hprod : h * (2 * m : ℝ) ≤ h * ((f.sourceDefect + f.targetDefect : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hcast hh
    have hm : (0 : ℝ) ≤ h * m := mul_nonneg hh (Nat.cast_nonneg _)
    linarith

namespace BlockEmbedding

/-! ### Counting over disjoint blocks -/

/-- Block points whose image under `p` lies in `K`, summed over the blocks, number at most
`|K|`. -/
theorem sum_card_filter_perm_embed_mem_le [Fintype I] (E : BlockEmbedding Y I)
    (p : Equiv.Perm Y) (K : Finset Y) :
    ∑ C, (Finset.univ.filter fun x : E.model C ↦ p (E.embed C x) ∈ K).card ≤ K.card := by
  have hsigma : (Finset.univ.sigma fun C ↦
      Finset.univ.filter fun x : E.model C ↦ p (E.embed C x) ∈ K).card =
      ∑ C, (Finset.univ.filter fun x : E.model C ↦ p (E.embed C x) ∈ K).card :=
    Finset.card_sigma _ _
  rw [← hsigma]
  refine Finset.card_le_card_of_injOn (fun d : Σ C, E.model C ↦ p (E.embed d.1 d.2)) ?_ ?_
  · rintro ⟨C, x⟩ hd
    have hd' := Finset.mem_sigma.mp (Finset.mem_coe.mp hd)
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp hd'.2).2
  · rintro ⟨C, x⟩ - ⟨C', x'⟩ - hxx
    have h₁ : E.embed C x = E.embed C' x' := p.injective hxx
    have hCC : C = C' := E.embed_disjoint C C' x x' h₁
    subst hCC
    have hx : x = x' := E.embed_injective C h₁
    subst hx
    rfl

/-- Block points lying in `K`, summed over the blocks, number at most `|K|`. -/
theorem sum_card_filter_embed_mem_le [Fintype I] (E : BlockEmbedding Y I) (K : Finset Y) :
    ∑ C, (Finset.univ.filter fun x : E.model C ↦ E.embed C x ∈ K).card ≤ K.card := by
  have hsigma : (Finset.univ.sigma fun C ↦
      Finset.univ.filter fun x : E.model C ↦ E.embed C x ∈ K).card =
      ∑ C, (Finset.univ.filter fun x : E.model C ↦ E.embed C x ∈ K).card :=
    Finset.card_sigma _ _
  rw [← hsigma]
  refine Finset.card_le_card_of_injOn (fun d : Σ C, E.model C ↦ E.embed d.1 d.2) ?_ ?_
  · rintro ⟨C, x⟩ hd
    have hd' := Finset.mem_sigma.mp (Finset.mem_coe.mp hd)
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp hd'.2).2
  · rintro ⟨C, x⟩ - ⟨C', x'⟩ - hxx
    have h₁ : E.embed C x = E.embed C' x' := hxx
    have hCC : C = C' := E.embed_disjoint C C' x x' h₁
    subst hCC
    have hx : x = x' := E.embed_injective C h₁
    subst hx
    rfl

/-! ### Uniqueness of candidate bridges -/

/-- Bridges out of one block into distinct blocks have disjoint sources. -/
theorem disjoint_bridge_source (E : BlockEmbedding Y I) (q : Equiv.Perm Y) (C : I)
    {D D' : I} (hDD : D ≠ D') :
    Disjoint (E.bridge q C D).source (E.bridge q C D').source := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨z, hz⟩ := (E.mem_bridgeSource q C D x).mp hx
  obtain ⟨z', hz'⟩ := (E.mem_bridgeSource q C D' x).mp hx'
  exact hDD (E.embed_disjoint D D' z z' (hz.trans hz'.symm))

/-- Bridges from distinct blocks into one block have disjoint targets. -/
theorem disjoint_bridge_target (E : BlockEmbedding Y I) (q : Equiv.Perm Y) {C C' : I}
    (D : I) (hCC : C ≠ C') :
    Disjoint (E.bridge q C D).target (E.bridge q C' D).target := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨x, hx⟩ := (E.mem_bridgeTarget q C D z).mp hz
  obtain ⟨x', hx'⟩ := (E.mem_bridgeTarget q C' D z).mp hz'
  exact hCC (E.embed_disjoint C C' x x' (hx.trans hx'.symm))

/-- **A block has at most one candidate bridge.** -/
theorem eq_of_isClusterCandidate_bridge {L : Type*} [Fintype L] (E : BlockEmbedding Y I)
    (q : Equiv.Perm Y) {C D D' : I} (actC : L → Equiv.Perm (E.model C))
    (actD : L → Equiv.Perm (E.model D)) (actD' : L → Equiv.Perm (E.model D'))
    {h : ℝ} {m : ℕ} (hsize : 17 * m ≤ Fintype.card (E.model C))
    (hD : (E.bridge q C D).IsClusterCandidate actC actD h m)
    (hD' : (E.bridge q C D').IsClusterCandidate actC actD' h m) : D = D' := by
  by_contra hne
  have hcard := card_le_sourceDefect_add_of_disjoint (E.bridge q C D) (E.bridge q C D')
    (E.disjoint_bridge_source q C hne)
  have h₁ := hD.selfSmall
  have h₂ := hD'.selfSmall
  omega

/-- **A block receives at most one candidate bridge.** -/
theorem eq_of_isClusterCandidate_bridge_target {L : Type*} [Fintype L]
    (E : BlockEmbedding Y I) (q : Equiv.Perm Y) {C C' D : I}
    (actC : L → Equiv.Perm (E.model C)) (actC' : L → Equiv.Perm (E.model C'))
    (actD : L → Equiv.Perm (E.model D))
    {h : ℝ} {m : ℕ} (hsize : 17 * m ≤ Fintype.card (E.model D))
    (hC : (E.bridge q C D).IsClusterCandidate actC actD h m)
    (hC' : (E.bridge q C' D).IsClusterCandidate actC' actD h m) : C = C' := by
  by_contra hne
  have hcard := card_le_targetDefect_add_of_disjoint (E.bridge q C D) (E.bridge q C' D)
    (E.disjoint_bridge_target q D hne)
  have h₁ := hC.selfSmall
  have h₂ := hC'.selfSmall
  omega

end BlockEmbedding

namespace BlockAction

variable {E : BlockEmbedding Y I} {L : Type*}

/-! ### Local obstructions -/

/-- Ambient points at which a permutation `q` fails to commute with the label `s`. -/
def commutationFailure (A : BlockAction E L) (q : Equiv.Perm Y) (s : L) : Finset Y :=
  hammingDisagreement (q * A.act s) (A.act s * q)

theorem mem_commutationFailure (A : BlockAction E L) (q : Equiv.Perm Y) (s : L) (y : Y) :
    y ∈ A.commutationFailure q s ↔ q (A.act s y) ≠ A.act s (q y) :=
  mem_hammingDisagreement (q * A.act s) (A.act s * q) y

/-- The points of block `C` carrying a local obstruction for the label `s`: `q` fails to
commute with `s` at the point, the block action of `s` disagrees with the ambient action
there, or the image of the point under `q` meets such a disagreement in some block. -/
noncomputable def localObstruction [Fintype I] (A : BlockAction E L) (q : Equiv.Perm Y)
    (C : I) (s : L) : Finset (E.model C) := by
  classical
  exact Finset.univ.filter fun x ↦
    E.embed C x ∈ A.commutationFailure q s ∨ x ∈ A.compatFailure C s ∨
      q (E.embed C x) ∈ A.globalCompatFailure s

theorem mem_localObstruction [Fintype I] (A : BlockAction E L) (q : Equiv.Perm Y)
    (C : I) (s : L) (x : E.model C) :
    x ∈ A.localObstruction q C s ↔
      E.embed C x ∈ A.commutationFailure q s ∨ x ∈ A.compatFailure C s ∨
        q (E.embed C x) ∈ A.globalCompatFailure s := by
  classical
  simp [localObstruction]

/-- A local obstruction is a commutation failure, a compatibility failure of the block, or
a point sent to a compatibility failure. -/
theorem card_localObstruction_le [Fintype I] (A : BlockAction E L) (q : Equiv.Perm Y)
    (C : I) (s : L) :
    (A.localObstruction q C s).card ≤
      (Finset.univ.filter fun x : E.model C ↦ E.embed C x ∈ A.commutationFailure q s).card +
        (A.compatFailure C s).card +
        (Finset.univ.filter fun x : E.model C ↦
          q (E.embed C x) ∈ A.globalCompatFailure s).card := by
  refine (Finset.card_le_card (t := ((Finset.univ.filter fun x : E.model C ↦
      E.embed C x ∈ A.commutationFailure q s) ∪ A.compatFailure C s) ∪
      Finset.univ.filter fun x : E.model C ↦
        q (E.embed C x) ∈ A.globalCompatFailure s) ?_).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  intro x hx
  rcases (A.mem_localObstruction q C s x).mp hx with hc | hc | hc
  · exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ hc)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)

/-- **Local obstructions sum over the blocks.**  For every label they number at most the
commutation failures of `q` plus twice the compatibility failures of all blocks. -/
theorem sum_card_localObstruction_le [Fintype I] [Fintype L] (A : BlockAction E L)
    (q : Equiv.Perm Y) :
    ∑ C, ∑ s, (A.localObstruction q C s).card ≤
      ∑ s, ((A.commutationFailure q s).card + 2 * ∑ C, (A.compatFailure C s).card) := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun s _ ↦ ?_
  have h₁ := E.sum_card_filter_embed_mem_le (A.commutationFailure q s)
  have h₂ := E.sum_card_filter_perm_embed_mem_le q (A.globalCompatFailure s)
  have h₃ := A.card_globalCompatFailure_le s
  have h₄ : ∑ C, (A.localObstruction q C s).card ≤
      ∑ C, ((Finset.univ.filter fun x : E.model C ↦
          E.embed C x ∈ A.commutationFailure q s).card +
        (A.compatFailure C s).card +
        (Finset.univ.filter fun x : E.model C ↦
          q (E.embed C x) ∈ A.globalCompatFailure s).card) :=
    Finset.sum_le_sum fun C _ ↦ A.card_localObstruction_le q C s
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h₄
  omega

/-! ### Defects of maximal realizers -/

/-- Away from the local obstructions, a partial map realizing `p` intertwines the block
actions at `x`. -/
theorem embed_blockAct_apply_eq [Fintype I] (A : BlockAction E L) (p : Equiv.Perm Y)
    {C C' : I} (b : FinitePartialBijection (E.model C) (E.model C'))
    (hreal : ∀ x (hx : x ∈ b.source), E.embed C' (b.apply x hx) = p (E.embed C x))
    {s : L} {x : E.model C} (hx : x ∈ b.source) (hLO : x ∉ A.localObstruction p C s) :
    E.embed C' (A.blockAct C' s (b.apply x hx)) = p (E.embed C (A.blockAct C s x)) := by
  have hcomm : p (A.act s (E.embed C x)) = A.act s (p (E.embed C x)) := by
    by_contra hne
    exact hLO ((A.mem_localObstruction p C s x).mpr
      (Or.inl ((A.mem_commutationFailure p s _).mpr hne)))
  have hcompatC : x ∉ A.compatFailure C s := fun hmem ↦
    hLO ((A.mem_localObstruction p C s x).mpr (Or.inr (Or.inl hmem)))
  have hz := hreal x hx
  have hnotD : b.apply x hx ∉ A.compatFailure C' s := by
    intro hmem
    apply hLO
    refine (A.mem_localObstruction p C s x).mpr (Or.inr (Or.inr ?_))
    rw [← hz]
    exact A.embed_mem_globalCompatFailure hmem
  rw [A.embed_blockAct_of_not_mem hnotD, hz, A.embed_blockAct_of_not_mem hcompatC, hcomm]

/-- **Local forward defect.**  Let `b` realize `p` on its source and contain every point of
block `C` that `p` carries into block `C'`.  At every label its equivariance defect consists
of missing source points and local obstructions of `p`. -/
theorem card_equivarianceDefect_le_localObstruction [Fintype I] [Fintype L]
    (A : BlockAction E L) (p : Equiv.Perm Y) {C C' : I}
    (b : FinitePartialBijection (E.model C) (E.model C'))
    (hreal : ∀ x (hx : x ∈ b.source), E.embed C' (b.apply x hx) = p (E.embed C x))
    (hmax : ∀ x (z : E.model C'), E.embed C' z = p (E.embed C x) → x ∈ b.source) :
    (b.equivarianceDefect (A.blockAct C) (A.blockAct C')).card ≤
      ∑ s : L, (b.sourceDefect + (A.localObstruction p C s).card) := by
  classical
  have hsd : (Finset.univ \ b.source).card ≤ b.sourceDefect := by
    have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ b.source)
    rw [Finset.card_univ] at hsplit
    unfold FinitePartialBijection.sourceDefect
    omega
  refine (BlockEmbedding.card_le_sum_labelSlices _).trans
    (Finset.sum_le_sum fun s _ ↦ ?_)
  refine (Finset.card_le_card (t := (Finset.univ \ b.source) ∪ A.localObstruction p C s)
    ?_).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_right hsd _))
  intro x hx
  by_cases h₀ : x ∈ b.source
  swap
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h₀⟩)
  by_cases h₁ : x ∈ A.localObstruction p C s
  · exact Finset.mem_union_right _ h₁
  exfalso
  have hkey := A.embed_blockAct_apply_eq p b hreal h₀ h₁
  have hsrc : A.blockAct C s x ∈ b.source := hmax _ _ hkey
  have hdef := (Finset.mem_filter.mp hx).2
  rw [mem_equivarianceDefect] at hdef
  dsimp only at hdef
  apply hdef h₀ hsrc
  apply E.embed_injective C'
  rw [hreal _ hsrc, hkey]

/-- **Forward defect of a bridge**, charged block by block. -/
theorem card_equivarianceDefect_bridge_le_localObstruction [Fintype I] [Fintype L]
    (A : BlockAction E L) (q : Equiv.Perm Y) (C D : I) :
    ((E.bridge q C D).equivarianceDefect (A.blockAct C) (A.blockAct D)).card ≤
      ∑ s : L, ((E.bridge q C D).sourceDefect + (A.localObstruction q C s).card) :=
  A.card_equivarianceDefect_le_localObstruction q (E.bridge q C D)
    (E.embed_bridge_apply q C D)
    (fun x z hz ↦ (E.mem_bridgeSource q C D x).mpr ⟨z, hz⟩)

/-- **Backward defect of a bridge**, charged block by block. -/
theorem card_symm_equivarianceDefect_bridge_le_localObstruction [Fintype I] [Fintype L]
    (A : BlockAction E L) (q : Equiv.Perm Y) (C D : I) :
    ((E.bridge q C D).symm.equivarianceDefect (A.blockAct D) (A.blockAct C)).card ≤
      ∑ s : L, ((E.bridge q C D).targetDefect + (A.localObstruction q⁻¹ D s).card) :=
  A.card_equivarianceDefect_le_localObstruction q⁻¹ (E.bridge q C D).symm
    (E.embed_bridge_symm_apply q C D)
    (fun z x hx ↦ (E.mem_bridgeTarget q C D z).mpr ⟨x, hx⟩)

/-! ### Missing mass of a bridge -/

/-- **The source of a maximal realizer is almost invariant.**  A labelled boundary arc of
its source is a local obstruction of `p`, or it enters the source from a point that `p`
does not send into block `C'`, which charges a compatibility failure of block `C'`. -/
theorem card_taggedBoundary_source_le [Fintype I] [Fintype L]
    (A : BlockAction E L) (p : Equiv.Perm Y) {C C' : I}
    (b : FinitePartialBijection (E.model C) (E.model C'))
    (hreal : ∀ x (hx : x ∈ b.source), E.embed C' (b.apply x hx) = p (E.embed C x))
    (hmax : ∀ x (z : E.model C'), E.embed C' z = p (E.embed C x) → x ∈ b.source) :
    (taggedBoundary (A.blockAct C) b.source).card ≤
      ∑ s : L, ((A.localObstruction p C s).card + (A.compatFailure C' s).card) := by
  classical
  refine (BlockEmbedding.card_le_sum_labelSlices _).trans
    (Finset.sum_le_sum fun s _ ↦ ?_)
  have himage : (Finset.univ.filter fun x : E.model C ↦ x ∉ b.source ∧
      A.blockAct C s x ∈ b.source ∧ x ∉ A.localObstruction p C s).card ≤
      (A.compatFailure C' s).card := by
    refine le_trans ?_ (Finset.card_image_le (s := A.compatFailure C' s)
      (f := fun w ↦ (A.act s).symm (E.embed C' (A.blockAct C' s w))))
    refine Finset.card_le_card_of_injOn (fun x ↦ p (E.embed C x)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe] at hx ⊢
      obtain ⟨hout, hin, hLO⟩ := (Finset.mem_filter.mp hx).2
      have hcomm : p (A.act s (E.embed C x)) = A.act s (p (E.embed C x)) := by
        by_contra hne
        exact hLO ((A.mem_localObstruction p C s x).mpr
          (Or.inl ((A.mem_commutationFailure p s _).mpr hne)))
      have hcompatC : x ∉ A.compatFailure C s := fun hmem ↦
        hLO ((A.mem_localObstruction p C s x).mpr (Or.inr (Or.inl hmem)))
      have hamb : E.embed C' (b.apply _ hin) = A.act s (p (E.embed C x)) := by
        rw [hreal _ hin, A.embed_blockAct_of_not_mem hcompatC, hcomm]
      refine Finset.mem_image.mpr ⟨(A.blockAct C' s).symm (b.apply _ hin), ?_, ?_⟩
      · by_contra hw
        have hcw := A.embed_blockAct_of_not_mem hw
        rw [Equiv.apply_symm_apply, hamb] at hcw
        exact hout (hmax x _ ((A.act s).injective hcw).symm)
      · show (A.act s).symm (E.embed C' (A.blockAct C' s
          ((A.blockAct C' s).symm (b.apply _ hin)))) = p (E.embed C x)
        rw [Equiv.apply_symm_apply, hamb, Equiv.symm_apply_apply]
    · intro x _ x' _ hxx
      exact E.embed_injective C (p.injective hxx)
  refine (Finset.card_le_card (t := A.localObstruction p C s ∪
      Finset.univ.filter fun x : E.model C ↦ x ∉ b.source ∧
        A.blockAct C s x ∈ b.source ∧ x ∉ A.localObstruction p C s) ?_).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left himage _))
  intro x hx
  have hbd := (Finset.mem_filter.mp hx).2
  rw [mem_taggedBoundary] at hbd
  dsimp only at hbd
  by_cases hLO : x ∈ A.localObstruction p C s
  · exact Finset.mem_union_left _ hLO
  refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
  rcases hbd with ⟨hin, hout⟩ | ⟨hout, hin⟩
  · exact (hout (hmax _ _ (A.embed_blockAct_apply_eq p b hreal hin hLO))).elim
  · exact ⟨hout, hin, hLO⟩

/-- **Missing source mass by re-separation.**  If the local obstructions of `q` on block `C`
and the compatibility failures of block `D` are below `h` times a scale `⌊x⌋₊ + 1` at which
block `C` expands, a bridge carrying at least half of block `C` misses at most `x` of its
points. -/
theorem sourceDefect_bridge_le_of_reseparation [Fintype I] [Fintype L]
    (A : BlockAction E L) (q : Equiv.Perm Y) (C D : I) {h x : ℝ} (hx : 0 ≤ x)
    (hexp : HasTaggedExpansionAtScale (A.blockAct C) h (⌊x⌋₊ + 1))
    (hbd : ((∑ s : L, ((A.localObstruction q C s).card + (A.compatFailure D s).card) : ℕ) :
      ℝ) < h * ((⌊x⌋₊ + 1 : ℕ) : ℝ))
    (hmaj : 2 * (E.bridge q C D).sourceDefect ≤ Fintype.card (E.model C)) :
    ((E.bridge q C D).sourceDefect : ℝ) ≤ x := by
  have hsd : (Finset.univ \ (E.bridge q C D).source).card =
      (E.bridge q C D).sourceDefect := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [FinitePartialBijection.sourceDefect]
  have hle := A.card_taggedBoundary_source_le q (E.bridge q C D) (E.embed_bridge_apply q C D)
    (fun y z hz ↦ (E.mem_bridgeSource q C D y).mpr ⟨z, hz⟩)
  have hcast : ((taggedBoundary (A.blockAct C) (E.bridge q C D).source).card : ℝ) ≤
      ((∑ s : L, ((A.localObstruction q C s).card + (A.compatFailure D s).card) : ℕ) :
        ℝ) := by
    exact_mod_cast hle
  have hmain := card_compl_le_of_taggedBoundary (A.blockAct C) hx (E.bridge q C D).source
    hexp (lt_of_le_of_lt hcast hbd) (by rw [hsd]; exact hmaj)
  rwa [hsd] at hmain

/-- **Missing target mass by re-separation**, the same estimate for `q⁻¹` on block `D`. -/
theorem targetDefect_bridge_le_of_reseparation [Fintype I] [Fintype L]
    (A : BlockAction E L) (q : Equiv.Perm Y) (C D : I) {h x : ℝ} (hx : 0 ≤ x)
    (hexp : HasTaggedExpansionAtScale (A.blockAct D) h (⌊x⌋₊ + 1))
    (hbd : ((∑ s : L, ((A.localObstruction q⁻¹ D s).card + (A.compatFailure C s).card) :
      ℕ) : ℝ) < h * ((⌊x⌋₊ + 1 : ℕ) : ℝ))
    (hmaj : 2 * (E.bridge q C D).targetDefect ≤ Fintype.card (E.model D)) :
    ((E.bridge q C D).targetDefect : ℝ) ≤ x := by
  have hsd : (Finset.univ \ (E.bridge q C D).symm.source).card =
      (E.bridge q C D).targetDefect := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [FinitePartialBijection.targetDefect]
  have hle := A.card_taggedBoundary_source_le q⁻¹ (E.bridge q C D).symm
    (E.embed_bridge_symm_apply q C D)
    (fun z y hy ↦ (E.mem_bridgeTarget q C D z).mpr ⟨y, hy⟩)
  have hcast : ((taggedBoundary (A.blockAct D) (E.bridge q C D).symm.source).card : ℝ) ≤
      ((∑ s : L, ((A.localObstruction q⁻¹ D s).card + (A.compatFailure C s).card) : ℕ) :
        ℝ) := by
    exact_mod_cast hle
  have hmain := card_compl_le_of_taggedBoundary (A.blockAct D) hx
    (E.bridge q C D).symm.source hexp (lt_of_le_of_lt hcast hbd) (by rw [hsd]; exact hmaj)
  rwa [hsd] at hmain

end BlockAction

end BlockPatching
end GroupApproximation
