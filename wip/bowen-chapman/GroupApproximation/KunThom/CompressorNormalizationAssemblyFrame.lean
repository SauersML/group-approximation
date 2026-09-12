import GroupApproximation.KunThom.CompressorNormalizationAssembly
import GroupApproximation.KunThom.FixedPointNormalizationScaledBisection
import GroupApproximation.KunThom.BisectionActualDefect
import GroupApproximation.KunThom.NormalizationFromCriterionClosure

/-!
# The cluster frame of the per-compressor assembly

`seqNormalizes_of_compressor_of_steps` runs over abstract decompositions and
cluster frames.  This module fixes both.

* `RetainedData Γ A`: a finite generating set of `Γ` containing `1`, a
  `ComponentFamily` of `Γ` on it (the retained expander components with
  their completed labels), and the placement of every object as a block of the
  model.  `RetainedComponents Γ A` adds that the uncovered mass and the
  compatibility failures of the generator labels are negligible.
* `restrictFrom F N₀`: the component family with no objects before index `N₀`.
  Repair and improvement statements that hold from `N₀` on hold for it at every
  index.
* `ClusterFrame R`: a candidate threshold, a distance factor and a start index
  from which pair-scale repair and improvement hold.  At every index,
  `ClusterFrame.system` is the scaled cluster system of the restricted family,
  `ClusterFrame.Bis` its total bisections, and `ClusterFrame.patch` the patched
  permutation of a bisection (`BlockPatching.scaledBisectionArrows`).
* `ClusterFrame.almostCommutes_patch`: once the threshold vanishes, patched
  total bisections almost commute with `A(Γ)`.  Every arrow is a cluster
  candidate, so its equivariance defect is below the threshold times its block
  size; the uncovered mass and the compatibility failures are negligible; and
  almost commutation spreads from the generators to `Γ`.  This is the converse
  half of Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4), and discharges `hconv`.
-/

namespace GroupApproximation
namespace CompressorNormalizationAssembly

open CentralizerNormalizationImprove

/-! ### Component families from an index on -/

/-- The component family with no objects before index `N₀`. -/
@[reducible] def restrictFrom {K : Type} [Group K] {T : Finset K}
    (F : ComponentFamily K T) (N₀ : ℕ) : ComponentFamily K T where
  index n := {i : F.index n // N₀ ≤ n}
  model n i := F.model n i.1
  act n i := F.act n i.1
  cheeger := F.cheeger
  cheeger_pos := F.cheeger_pos
  expands n i := F.expands n i.1
  size_tendsTo M := by
    obtain ⟨N, hN⟩ := F.size_tendsTo M
    exact ⟨N, fun n hn i ↦ hN n hn i.1⟩
  locallyMultiplicative g h ε hε := by
    obtain ⟨N, hN⟩ := F.locallyMultiplicative g h ε hε
    exact ⟨N, fun n hn i ↦ hN n hn i.1⟩
  labelsInjective := by
    obtain ⟨N, hN⟩ := F.labelsInjective
    exact ⟨N, fun n hn i ↦ hN n hn i.1⟩

instance restrictFromFintype {K : Type} [Group K] {T : Finset K}
    (F : ComponentFamily K T) (N₀ n : ℕ) [Fintype (F.index n)] :
    Fintype ((restrictFrom F N₀).index n) :=
  inferInstanceAs (Fintype {i : F.index n // N₀ ≤ n})

/-- Repair from `N₀` on is repair of the restricted family at every index. -/
theorem pairRepairAt_restrictFrom {K : Type} [Group K] {T : Finset K}
    {F : ComponentFamily K T} {N₀ n : ℕ} {K₀ h d : ℝ}
    (hrep : N₀ ≤ n → F.PairRepairAt K₀ h d n) :
    (restrictFrom F N₀).PairRepairAt K₀ h d n := by
  intro i l b hb hb'
  exact hrep i.2 i.1 l.1 b hb hb'

/-- Improvement from `N₀` on is improvement of the restricted family at every
index. -/
theorem pairImproveCloseAt_restrictFrom {K : Type} [Group K] {T : Finset K}
    {F : ComponentFamily K T} {N₀ n : ℕ} {h d : ℝ}
    (himp : N₀ ≤ n → F.PairImproveCloseAt h d n) :
    (restrictFrom F N₀).PairImproveCloseAt h d n := by
  intro i j l f hf g hg
  exact himp i.2 i.1 j.1 l.1 f hf g hg

/-- A sum over the objects satisfying a proposition is at most the full sum of
a nonnegative function. -/
theorem sum_subtype_val_le {ι : Type*} [Fintype ι] (p : Prop) [Decidable p] (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) :
    ∑ X : {i : ι // p}, c X.1 ≤ ∑ i, c i := by
  have hmap : ∑ i ∈ (Finset.univ : Finset {i : ι // p}).map
      (Function.Embedding.subtype fun _ ↦ p), c i = ∑ X : {i : ι // p}, c X.1 :=
    Finset.sum_map _ _ _
  rw [← hmap]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ hc i

/-! ### Retained components -/

/-- Retained components of `A|Γ`: a component family on a finite generating set
of `Γ` containing `1`, placed as disjoint blocks of the models. -/
structure RetainedData {G : Type} [Group G] (Γ : Subgroup G) (A : SoficApproximation G) where
  generators : Finset ↥Γ
  one_mem : (1 : ↥Γ) ∈ generators
  generate : Subgroup.closure (generators : Set ↥Γ) = ⊤
  family : ComponentFamily ↥Γ generators
  fintypeIndex : ∀ n, Fintype (family.index n)
  embed : ∀ n (i : family.index n), family.model n i → A.model n
  embed_injective : ∀ n i, Function.Injective (embed n i)
  embed_disjoint : ∀ n (i j : family.index n) (x : family.model n i) (z : family.model n j),
    embed n i x = embed n j z → i = j

namespace RetainedData

instance instFintypeIndex {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    (R : RetainedData Γ A) (n : ℕ) : Fintype (R.family.index n) :=
  R.fintypeIndex n

instance instNonemptyGenerators {G : Type} [Group G] {Γ : Subgroup G}
    {A : SoficApproximation G} (R : RetainedData Γ A) : Nonempty ↥R.generators :=
  ⟨⟨1, R.one_mem⟩⟩

/-- The retained components as blocks of the model at index `n`. -/
def embedding {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    (R : RetainedData Γ A) (n : ℕ) :
    BlockPatching.BlockEmbedding (A.model n) (R.family.index n) where
  model := R.family.model n
  embed := R.embed n
  embed_injective := R.embed_injective n
  embed_disjoint := R.embed_disjoint n

/-- The ambient generator labels, and the completed labels on the blocks. -/
def blockAction {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    (R : RetainedData Γ A) (n : ℕ) :
    BlockPatching.BlockAction (R.embedding n) ↥R.generators where
  act s := A.map n ((s : ↥Γ) : G)
  blockAct i := R.family.tags n i

end RetainedData

/-- Retained components whose uncovered mass and generator compatibility
failures are negligible. -/
structure RetainedComponents {G : Type} [Group G] (Γ : Subgroup G)
    (A : SoficApproximation G) where
  data : RetainedData Γ A
  uncovered_negligible : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
    fun n ↦ ((data.embedding n).uncovered.card : ℝ)
  compat_negligible : ∀ s : ↥data.generators,
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ∑ i, (((data.blockAction n).compatFailure i s).card : ℝ)

/-! ### Cluster frames -/

/-- A candidate threshold, a distance factor and a start index from which the
pair-scale repair and improvement statements hold. -/
structure ClusterFrame {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    (R : RetainedComponents Γ A) where
  threshold : ℕ → ℝ
  distance : ℕ → ℝ
  start : ℕ
  threshold_pos : ∀ n, 0 < threshold n
  threshold_small : ∀ n, threshold n ≤ 1 / 100000
  threshold_cheeger : ∀ n, threshold n ≤ R.data.family.cheeger
  scale_large : ∀ n, start ≤ n → ∀ i, 20 ≤ R.data.family.scale n i
  repair : ∀ n, start ≤ n → R.data.family.PairRepairAt 4 (threshold n) (distance n) n
  improve : ∀ n, start ≤ n → R.data.family.PairImproveCloseAt (threshold n) (distance n) n

namespace ClusterFrame

open Classical

/-- The retained objects at index `n`: none before the start. -/
abbrev Obj {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) : Type :=
  (restrictFrom R.data.family F.start).index n

/-- The scaled cluster system at index `n`. -/
noncomputable def system {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) :=
  (restrictFrom R.data.family F.start).clusterSystem n (F.threshold_pos n)
    (F.threshold_small n) (F.threshold_cheeger n) (fun i ↦ F.scale_large n i.2 i.1)
    (pairRepairAt_restrictFrom fun hn ↦ F.repair n hn)
    (pairImproveCloseAt_restrictFrom fun hn ↦ F.improve n hn)

/-- Total bisections of the cluster groupoid at index `n`. -/
abbrev Bis {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) : Type :=
  FiniteGroupoid.Bisection (F.system n).presentation.Obj

/-- The placement of an object of the cluster system. -/
def embedAt {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) (X : F.Obj n) :
    (F.system n).model X → A.model n :=
  R.data.embed n X.1

theorem embedAt_injective {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) (X : F.Obj n) :
    Function.Injective (F.embedAt n X) :=
  R.data.embed_injective n X.1

theorem embedAt_disjoint {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) (X X' : F.Obj n)
    (x : (F.system n).model X) (z : (F.system n).model X')
    (h : F.embedAt n X x = F.embedAt n X' z) : X = X' :=
  Subtype.ext (R.data.embed_disjoint n X.1 X'.1 x z h)

/-- The objects of the cluster system as blocks of the model. -/
def embedding {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) :
    BlockPatching.BlockEmbedding (A.model n) (F.Obj n) :=
  BlockPatching.scaledClusterEmbedding (F.system n).clusterData (F.embedAt n)
    (F.embedAt_injective n) (F.embedAt_disjoint n)

/-- The block arrows of a total bisection: one chosen candidate per object. -/
noncomputable def arrows {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) (b : F.Bis n) :
    BlockPatching.BlockArrows (F.embedding n) :=
  BlockPatching.scaledBisectionArrows (D := (F.system n).clusterData) (F.embedAt n)
    (F.embedAt_injective n) (F.embedAt_disjoint n) b

/-- The patched permutation of a total bisection. -/
noncomputable def patch {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) (b : F.Bis n) :
    Equiv.Perm (A.model n) :=
  (F.arrows n b).patch

/-- The generator labels on the model and on the objects. -/
def action {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) :
    BlockPatching.BlockAction (F.embedding n) ↥R.data.generators :=
  BlockPatching.scaledClusterAction (D := (F.system n).clusterData) (F.embedAt n)
    (F.embedAt_injective n) (F.embedAt_disjoint n) (fun s ↦ A.map n ((s : ↥Γ) : G))
    (F.system n).act

/-- Every block arrow of a total bisection is a cluster candidate at the pair
scale. -/
theorem arrows_isClusterCandidate {G : Type} [Group G] {Γ : Subgroup G}
    {A : SoficApproximation G} {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ)
    (b : F.Bis n) (X : F.Obj n) :
    ((F.arrows n b).arrow X).IsClusterCandidate ((F.system n).act X)
      ((F.system n).act (BlockPatching.scaledBisectionIndexEquiv
        (D := (F.system n).clusterData) b X)) (F.threshold n)
      (min ((F.system n).scale X) ((F.system n).scale
        (BlockPatching.scaledBisectionIndexEquiv (D := (F.system n).clusterData) b X))) :=
  (FinitePartialBijection.mem_clusterCandidates ((F.system n).act X)
    ((F.system n).act (BlockPatching.scaledBisectionIndexEquiv
      (D := (F.system n).clusterData) b X)) (F.threshold n)
    (min ((F.system n).scale X) ((F.system n).scale
      (BlockPatching.scaledBisectionIndexEquiv (D := (F.system n).clusterData) b X)))
    ((F.arrows n b).arrow X)).mp
    (BlockPatching.scaledBisectionRep (D := (F.system n).clusterData) b X).2

/-- From the start on, a point covered by no retained block is covered by no
object of the frame. -/
theorem uncovered_subset {G : Type} [Group G] {Γ : Subgroup G} {A : SoficApproximation G}
    {R : RetainedComponents Γ A} (F : ClusterFrame R) (n : ℕ) (hn : F.start ≤ n) :
    (F.embedding n).uncovered ⊆ (R.data.embedding n).uncovered := by
  intro y hy
  rw [BlockPatching.BlockEmbedding.mem_uncovered] at hy ⊢
  intro i x hx
  exact hy (⟨i, hn⟩ : {i : R.data.family.index n // F.start ≤ n}) x hx

/-- The uncovered mass of the frame is negligible. -/
theorem uncovered_negligible {G : Type} [Group G] {Γ : Subgroup G}
    {A : SoficApproximation G} {R : RetainedComponents Γ A} (F : ClusterFrame R) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ((F.embedding n).uncovered.card : ℝ) := by
  refine Vanishing.squeeze_eventually R.uncovered_negligible F.start fun n hn ↦ ⟨?_, ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast Finset.card_le_card (F.uncovered_subset n hn)

/-- The compatibility failures of a generator label on the frame are negligible. -/
theorem compat_negligible {G : Type} [Group G] {Γ : Subgroup G}
    {A : SoficApproximation G} {R : RetainedComponents Γ A} (F : ClusterFrame R)
    (s : ↥R.data.generators) :
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ∑ X, (((F.action n).compatFailure X s).card : ℝ) := by
  refine Vanishing.squeeze_eventually (R.compat_negligible s) F.start fun n _ ↦ ⟨?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hsets : ∀ X : F.Obj n,
        (F.action n).compatFailure X s = (R.data.blockAction n).compatFailure X.1 s :=
      fun _ ↦ rfl
    have hle := sum_subtype_val_le (F.start ≤ n)
      (fun i ↦ (((R.data.blockAction n).compatFailure i s).card : ℝ))
      (fun _ ↦ Nat.cast_nonneg _)
    calc ∑ X : F.Obj n, (((F.action n).compatFailure X s).card : ℝ)
        = ∑ X : F.Obj n, (((R.data.blockAction n).compatFailure X.1 s).card : ℝ) :=
          Finset.sum_congr rfl fun X _ ↦ by rw [hsets X]
      _ ≤ ∑ i, (((R.data.blockAction n).compatFailure i s).card : ℝ) := hle

/-- **Patched total bisections almost commute with `A(Γ)`.**  The converse half
of Kun--Thom Lemma 4.2(4), for a frame whose threshold vanishes. -/
theorem almostCommutes_patch {G : Type} [Group G] {Γ : Subgroup G}
    {A : SoficApproximation G} {R : RetainedComponents Γ A} (F : ClusterFrame R)
    (hthr : Vanishing F.threshold) (b : ∀ n, F.Bis n) :
    ∀ γ ∈ Γ, A.AlmostCommutes (fun n ↦ F.patch n (b n)) γ := by
  refine A.almostCommutes_of_generators R.data.generators R.data.generate fun s hs ↦ ?_
  exact BlockPatching.vanishing_commutator_patch_of_candidates (fun n ↦ F.arrows n (b n))
    (fun n ↦ F.action n) ⟨s, hs⟩ F.threshold (fun n ↦ (F.threshold_pos n).le) hthr
    (fun n X ↦ min ((F.system n).scale X) ((F.system n).scale
      (BlockPatching.scaledBisectionIndexEquiv (D := (F.system n).clusterData) (b n) X)))
    (fun n X ↦ (F.system n).size_min_left X _)
    (fun n X ↦ F.arrows_isClusterCandidate n (b n) X)
    F.uncovered_negligible (F.compat_negligible ⟨s, hs⟩)

end ClusterFrame

end CompressorNormalizationAssembly
end GroupApproximation
