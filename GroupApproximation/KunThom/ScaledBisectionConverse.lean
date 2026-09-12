import GroupApproximation.KunThom.BisectionActualDefect
import GroupApproximation.KunThom.FixedPointNormalizationScaledBisection
import GroupApproximation.KunThom.NormalizationFromCriterionClosure

/-!
# The converse half at per-object scales, along a sofic approximation

Kun--Thom, arXiv:2608.06222v3, Lemma 4.2(4), converse half: every sequence of
patched bisections of allowed arrows represents an element of the centralizer
of `σ(Γ)`.  In `CompressorNormalizationAssembly` this is the hypothesis
`hconv`.  The frame there is a `ScaledPartialClusterSystem`, where an arrow from
`X` to `X'` is allowed at threshold `h` and scale `min (scale X) (scale X')`,
with `scale X = |X| / 18`.

The estimate is `BlockPatching.vanishing_commutator_patch_of_candidates`, which
holds for any block arrows that are candidates.  This file only instantiates it.

* `vanishing_commutator_scaledPatch_of_candidates`: along a sequence of scaled
  cluster systems placed disjointly in the models, block arrows that are
  candidates at the pair scales patch to permutations almost commuting with a
  label.  The hypotheses are threshold `h_n → 0`, negligible uncovered mass and
  negligible compatibility failures of that label.
* `scaledBisectionArrows_isClusterCandidate`: the chosen representatives of a
  bisection are candidates at the pair scales.
* `SoficApproximation.almostCommutes_of_labels`: almost commutation with the
  labels of a finite family generating `Γ` gives almost commutation with every
  `γ ∈ Γ`.
* `SoficApproximation.almostCommutes_scaledPatch_of_candidates` and
  `almostCommutes_scaledBisectionPatch`: the converse half along a sofic
  approximation, with labels acting through the approximation, for any
  candidate arrows and for the chosen representatives of bisections.
-/

namespace GroupApproximation
namespace BlockPatching

universe u

/-- **Vanishing commutation of patched scaled candidates.** -/
theorem vanishing_commutator_scaledPatch_of_candidates {Y : ℕ → FiniteModel}
    {I : ℕ → Type u} [∀ n, Fintype (I n)] {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] (D : ∀ n, ScaledPartialClusterSystem (I n) L)
    (ι : ∀ n X, (D n).model X → Y n) (hinj : ∀ n X, Function.Injective (ι n X))
    (hdisj : ∀ n (X X' : I n) (x : (D n).model X) (z : (D n).model X'),
      ι n X x = ι n X' z → X = X')
    (β : ∀ n, BlockArrows (scaledClusterEmbedding (D n).clusterData (ι n) (hinj n)
      (hdisj n)))
    (hcand : ∀ n X, ((β n).arrow X).IsClusterCandidate ((D n).act X)
      ((D n).act ((β n).objEquiv X)) (D n).h
        (min ((D n).scale X) ((D n).scale ((β n).objEquiv X))))
    (act : ∀ n, L → Equiv.Perm (Y n)) (s : L) (hh : Vanishing fun n ↦ (D n).h)
    (huncovered : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ((scaledClusterEmbedding (D n).clusterData (ι n) (hinj n)
        (hdisj n)).uncovered.card : ℝ))
    (hcompat : Negligible (fun n ↦ (Fintype.card (Y n) : ℝ)) fun n ↦
      ∑ X, (((scaledClusterAction (D := (D n).clusterData) (ι n) (hinj n) (hdisj n)
        (act n) (D n).act).compatFailure X s).card : ℝ)) :
    Vanishing fun n ↦ hammingDistance (Y n)
      ((β n).patch * act n s) (act n s * (β n).patch) :=
  vanishing_commutator_patch_of_candidates β
    (fun n ↦ scaledClusterAction (D := (D n).clusterData) (ι n) (hinj n) (hdisj n)
      (act n) (D n).act) s (fun n ↦ (D n).h) (fun n ↦ (D n).h_pos.le) hh
    (fun n X ↦ min ((D n).scale X) ((D n).scale ((β n).objEquiv X)))
    (fun n X ↦ (D n).size_min_left X ((β n).objEquiv X)) hcand huncovered hcompat

/-- The chosen representatives of a bisection of a scaled cluster system are
cluster candidates at the pair scales. -/
theorem scaledBisectionArrows_isClusterCandidate {I : Type u} [Fintype I] {L : Type*}
    [Fintype L] [DecidableEq L] [Nonempty L] {Y : FiniteModel}
    (D : ScaledPartialClusterSystem I L) (ι : ∀ X, D.model X → Y)
    (hinj : ∀ X, Function.Injective (ι X))
    (hdisj : ∀ (X X' : I) (x : D.model X) (z : D.model X'),
      ι X x = ι X' z → X = X')
    (b : FiniteGroupoid.Bisection D.presentation.Obj) (X : I) :
    ((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).arrow X
      ).IsClusterCandidate (D.act X)
        (D.act ((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).objEquiv X))
        D.h (min (D.scale X)
          (D.scale ((scaledBisectionArrows (D := D.clusterData) ι hinj hdisj b).objEquiv X))) :=
  (FinitePartialBijection.mem_clusterCandidates _ _ _ _ _).mp (scaledBisectionRep b X).2

end BlockPatching

namespace SoficApproximation

variable {G : Type} [Group G]

/-- **From labels to the subgroup.**  If a sequence almost commutes with the
models of the labels of a finite family generating `Γ`, it almost commutes with
the model of every element of `Γ`. -/
theorem almostCommutes_of_labels (A : SoficApproximation G) {Γ : Subgroup G}
    {L : Type*} [Fintype L] (lab : L → ↥Γ)
    (hgen : Subgroup.closure (Set.range lab) = ⊤) (p : ∀ n, Equiv.Perm (A.model n))
    (hlab : ∀ s, Vanishing fun n ↦ hammingDistance (A.model n)
      (p n * A.map n (lab s : G)) (A.map n (lab s : G) * p n)) :
    ∀ γ ∈ Γ, A.AlmostCommutes p γ := by
  classical
  refine A.almostCommutes_of_generators (Finset.univ.image lab) ?_ ?_
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hgen
  · intro s hs
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hs
    exact hlab l

/-- **The converse half along a sofic approximation.**  Scaled cluster systems
placed disjointly in the models of `A`, whose labels act through `A` and
generate `Γ`, with threshold `h_n → 0` and negligible uncovered mass and
compatibility failures: every patch of candidate arrows at the pair scales
almost commutes with every element of `Γ`. -/
theorem almostCommutes_scaledPatch_of_candidates (A : SoficApproximation G)
    {Γ : Subgroup G} {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (lab : L → ↥Γ) (hgen : Subgroup.closure (Set.range lab) = ⊤)
    {I : ℕ → Type u} [∀ n, Fintype (I n)] (D : ∀ n, ScaledPartialClusterSystem (I n) L)
    (ι : ∀ n X, (D n).model X → A.model n) (hinj : ∀ n X, Function.Injective (ι n X))
    (hdisj : ∀ n (X X' : I n) (x : (D n).model X) (z : (D n).model X'),
      ι n X x = ι n X' z → X = X')
    (β : ∀ n, BlockPatching.BlockArrows
      (BlockPatching.scaledClusterEmbedding (D n).clusterData (ι n) (hinj n) (hdisj n)))
    (hcand : ∀ n X, ((β n).arrow X).IsClusterCandidate ((D n).act X)
      ((D n).act ((β n).objEquiv X)) (D n).h
        (min ((D n).scale X) ((D n).scale ((β n).objEquiv X))))
    (hh : Vanishing fun n ↦ (D n).h)
    (huncovered : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((BlockPatching.scaledClusterEmbedding (D n).clusterData (ι n) (hinj n)
        (hdisj n)).uncovered.card : ℝ))
    (hcompat : ∀ s, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X, (((BlockPatching.scaledClusterAction (D := (D n).clusterData) (ι n) (hinj n)
        (hdisj n) (fun l ↦ A.map n (lab l : G)) (D n).act).compatFailure X s).card : ℝ)) :
    ∀ γ ∈ Γ, A.AlmostCommutes (fun n ↦ (β n).patch) γ :=
  A.almostCommutes_of_labels lab hgen (fun n ↦ (β n).patch) fun s ↦
    BlockPatching.vanishing_commutator_scaledPatch_of_candidates D ι hinj hdisj β hcand
      (fun n l ↦ A.map n (lab l : G)) s hh huncovered (hcompat s)

/-- **Patched bisections along a sofic approximation.**  The chosen
representatives of any sequence of bisections of scaled cluster systems, under
the hypotheses of `almostCommutes_scaledPatch_of_candidates`, patch to a
sequence almost commuting with every element of `Γ`. -/
theorem almostCommutes_scaledBisectionPatch (A : SoficApproximation G)
    {Γ : Subgroup G} {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (lab : L → ↥Γ) (hgen : Subgroup.closure (Set.range lab) = ⊤)
    {I : ℕ → Type u} [∀ n, Fintype (I n)] (D : ∀ n, ScaledPartialClusterSystem (I n) L)
    (ι : ∀ n X, (D n).model X → A.model n) (hinj : ∀ n X, Function.Injective (ι n X))
    (hdisj : ∀ n (X X' : I n) (x : (D n).model X) (z : (D n).model X'),
      ι n X x = ι n X' z → X = X')
    (b : ∀ n, FiniteGroupoid.Bisection (D n).presentation.Obj)
    (hh : Vanishing fun n ↦ (D n).h)
    (huncovered : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ((BlockPatching.scaledClusterEmbedding (D n).clusterData (ι n) (hinj n)
        (hdisj n)).uncovered.card : ℝ))
    (hcompat : ∀ s, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ X, (((BlockPatching.scaledClusterAction (D := (D n).clusterData) (ι n) (hinj n)
        (hdisj n) (fun l ↦ A.map n (lab l : G)) (D n).act).compatFailure X s).card : ℝ)) :
    ∀ γ ∈ Γ, A.AlmostCommutes (fun n ↦ (BlockPatching.scaledBisectionArrows
      (D := (D n).clusterData) (ι n) (hinj n) (hdisj n) (b n)).patch) γ :=
  A.almostCommutes_scaledPatch_of_candidates lab hgen D ι hinj hdisj
    (fun n ↦ BlockPatching.scaledBisectionArrows (D := (D n).clusterData) (ι n) (hinj n)
      (hdisj n) (b n))
    (fun n X ↦ BlockPatching.scaledBisectionArrows_isClusterCandidate (D n) (ι n) (hinj n)
      (hdisj n) (b n) X)
    hh huncovered hcompat

end SoficApproximation
end GroupApproximation
