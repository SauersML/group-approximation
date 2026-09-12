import GroupApproximation.KunThom.CompressorNormalizationAssemblyFrame
import GroupApproximation.KunThom.MedianVertexFormBlocks
import GroupApproximation.KunThom.ArrowCountMedianBlocks
import GroupApproximation.KunThom.CountingEndgameBundle

/-!
# The relative data and the counting Props of the per-compressor assembly

`CompressorNormalizationAssembly.seqNormalizes_of_compressor_of_frameSteps` runs
over cluster frames `F : ClusterFrame R` and takes as parameters a type of relative
data `Rel F` of the compressor `t`, and three Props about it: `OneSided`,
`Concentrated` and `Transported`.  This file fixes all four.

* `CompressorRelativeData t F`: a compression setup with `t` among its compressors,
  an ambient expander decomposition, negligible self-bridge mass of the embedded
  generators of `Γ`, and for every compressor `q` a matched family `matched q n`, a
  retained family `retained q n`, the bundled relative cluster functor of Kun and
  Thom's Lemma 4.3 between them, negligible weight outside both families, negligible
  missing bridge mass along the matching, and matched objects at most twice the size
  of their matches.
* `observable F n i`: the arrow count of the object `i` in the cluster groupoid at
  index `n`, the observable to which the median lemma is applied once
  (`ArrowCountMedian`).
* `CompressorRelativeData.OneSided`: the one-sided inequalities
  `f (π q n i) ≤ (1 + κ q n) f i` off a family `Bad q n` of negligible weight, with
  `κ q` vanishing, for every compressor.  These are the inputs `hκ`, `hκv`, `hone`
  and `hbad` of `MedianVertexForm.blockRatio_negligible`.
* `CompressorRelativeData.Concentrated`: the conclusion of `blockRatio_negligible`
  at `t`.  For every `η` with `0 < η` and `2η < 1`, the matched objects whose arrow
  counts violate the squared ratio bounds have negligible weight.
* `CompressorRelativeData.Transported a b`: a finite set `S n` of retained objects
  and a choice `sel n` of targets, with negligible weight outside the images of
  `S n`, such that at every object of `S n` the total bisection `b n` carries the
  inclusion of a preimage of the transported arrow of `a n`.  This is the conclusion
  of `GroupoidPresentation.RelativeClusterFunctor.exists_bisection_lift`.
-/

namespace GroupApproximation
namespace CountingEndgame

open CategoryTheory CompressorNormalizationAssembly GroupoidPresentation

universe u

/-- Representatives of a scaled cluster presentation form a finite type. -/
instance scaledPresentationRepFinite {I : Type u} [Fintype I] {L : Type*} [Fintype L]
    [DecidableEq L] [Nonempty L] (D : ScaledPartialClusterSystem I L) (X Y : I) :
    Finite (D.presentation.Rep X Y) :=
  inferInstanceAs (Finite (D.clusterData.Rep X Y))

open Classical in
/-- The arrow count of an object of the cluster groupoid of a frame at index `n`. -/
noncomputable def observable {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (F : ClusterFrame R) (n : ℕ)
    (i : F.Obj n) : ℕ :=
  ArrowCountMedian.arrowCount (⟨i⟩ : (F.system n).presentation.Obj)

open Classical in
/-- **Relative data of a compressor over a cluster frame.** -/
structure CompressorRelativeData {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} (t : G) (F : ClusterFrame R) where
  /-- The compression setup, with `t` among its compressors. -/
  setup : CompressionSetup G K PUnit.{1}
  mem_compressors : t ∈ setup.compressors
  /-- A symmetric generating set of `G` and an expander decomposition of `A` for it. -/
  ambientGenerators : Finset G
  ambient : ExpanderDecomposition A ambientGenerators
  ambientGenerators_symm : ∀ g ∈ ambientGenerators, g⁻¹ ∈ ambientGenerators
  ambientGenerators_generate : Subgroup.closure (ambientGenerators : Set G) = ⊤
  /-- The embedded generators of `Γ` carry every object to itself up to negligible
  missing mass. -/
  bridge_self_negligible : ∀ s ∈ setup.generatorsΓ,
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i, (((F.embedding n).bridge (A.map n (setup.embedΓ s)) i i).sourceDefect : ℝ)
  /-- The matched objects of every compressor. -/
  matched : G → ∀ n, Finset (F.Obj n)
  /-- The retained objects of every compressor. -/
  retained : G → ∀ n, Finset (F.Obj n)
  /-- The relative cluster functor of every compressor (Kun–Thom, Lemma 4.3). -/
  functor : ∀ q ∈ setup.compressors, ∀ n,
    (F.system n).presentation.RelativeClusterFunctor (retained q n) (matched q n)
  unmatched_negligible : ∀ q ∈ setup.compressors,
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ Finset.univ \ matched q n, (Fintype.card ((F.embedding n).model i) : ℝ)
  unretained_negligible : ∀ q ∈ setup.compressors,
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ Finset.univ \ retained q n, (Fintype.card ((F.embedding n).model i) : ℝ)
  bridge_negligible : ∀ (q : G) (hq : q ∈ setup.compressors),
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ matched q n,
        (((F.embedding n).bridge (A.map n q) i ((functor q hq n).π i)).sourceDefect : ℝ)
  size_le : ∀ (q : G) (hq : q ∈ setup.compressors) (n : ℕ), ∀ i ∈ matched q n,
    Fintype.card ((F.embedding n).model i) ≤
      2 * Fintype.card ((F.embedding n).model ((functor q hq n).π i))

namespace CompressorRelativeData

open Classical in
/-- The matching of a compressor, and the identity for any other element. -/
noncomputable def matching {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G} {F : ClusterFrame R}
    (M : CompressorRelativeData t F) (q : G) (n : ℕ) : F.Obj n → F.Obj n :=
  if hq : q ∈ M.setup.compressors then (M.functor q hq n).π else id

open Classical in
theorem matching_of_mem {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G} {F : ClusterFrame R}
    (M : CompressorRelativeData t F) {q : G} (hq : q ∈ M.setup.compressors) (n : ℕ) :
    M.matching q n = (M.functor q hq n).π := by
  rw [matching, dif_pos hq]

open Classical in
/-- The relative cluster functor of `t` at index `n`, followed by the inclusion of its
target restriction. -/
noncomputable def liftFunctor {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G} {F : ClusterFrame R}
    (M : CompressorRelativeData t F) (n : ℕ) :
    ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj ⥤
      (F.system n).presentation.Obj :=
  (M.functor t M.mem_compressors n).F.toFunctor ⋙
    (F.system n).presentation.restrictInclusionFunctor (M.matched t n : Set (F.Obj n))

open Classical in
/-- The inclusion of the retained objects of `t` at index `n`. -/
noncomputable def inclusion {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G} {F : ClusterFrame R}
    (M : CompressorRelativeData t F) (n : ℕ) :
    ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj ⥤
      (F.system n).presentation.Obj :=
  (F.system n).presentation.restrictInclusionFunctor (M.retained t n : Set (F.Obj n))

/-- **One-sided inequalities** (Kun–Thom (2) and (3), for the arrow count). -/
def OneSided {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G} {F : ClusterFrame R}
    (M : CompressorRelativeData t F) : Prop :=
  ∃ (κ : G → ℕ → ℝ) (Bad : G → ∀ n, Finset (F.Obj n)),
    (∀ q ∈ M.setup.compressors, ∀ n, 0 ≤ κ q n) ∧
    (∀ q ∈ M.setup.compressors, Vanishing (κ q)) ∧
    (∀ q ∈ M.setup.compressors, ∀ n, ∀ i ∈ M.matched q n, i ∉ Bad q n →
      (observable F n (M.matching q n i) : ℝ) ≤ (1 + κ q n) * observable F n i) ∧
    (∀ q ∈ M.setup.compressors, Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ))
      fun n ↦ ∑ i ∈ Bad q n, (Fintype.card ((F.embedding n).model i) : ℝ))

open Classical in
/-- **Concentration** (Kun–Thom (4), for the arrow count at `t`). -/
def Concentrated {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G} {F : ClusterFrame R}
    (M : CompressorRelativeData t F) : Prop :=
  ∀ η : ℝ, 0 < η → 2 * η < 1 →
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ (M.matched t n).filter (fun i ↦
          ¬ ((1 - 2 * η) ^ 2 * (observable F n (M.matching t n i) : ℝ) ≤
              (1 + 2 * η) ^ 2 * observable F n i ∧
            (1 - 2 * η) ^ 2 * (observable F n i : ℝ) ≤
              (1 + 2 * η) ^ 2 * observable F n (M.matching t n i))),
        (Fintype.card ((F.embedding n).model i) : ℝ)

open Classical in
/-- **Transported bisections** (the output of the counting in Kun–Thom's proof of
Theorem 4.1). -/
def Transported {G : Type} [Group G] {A : SoficApproximation G} {K : Type}
    [Group K] {ι : K →* G} {R : RetainedComponents A K ι} {t : G} {F : ClusterFrame R}
    (M : CompressorRelativeData t F) (a b : ∀ n, F.Bis n) : Prop :=
  ∃ (S : ∀ n, Finset ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj)
    (sel : ∀ n, ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj →
      ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj),
    Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (fun n ↦
      ∑ i ∈ Finset.univ \ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        (Fintype.card ((F.embedding n).model i) : ℝ)) ∧
    ∀ n, ∀ X ∈ S n,
      ∃ hsel : (M.liftFunctor n).obj (sel n X) = (a n).objEquiv ((M.liftFunctor n).obj X),
        ∃ g : X ⟶ sel n X,
          (M.liftFunctor n).map g = (a n).hom ((M.liftFunctor n).obj X) ≫ eqToHom hsel.symm ∧
          ∃ e : (b n).objEquiv ((M.inclusion n).obj X) = (M.inclusion n).obj (sel n X),
            (b n).hom ((M.inclusion n).obj X) ≫ eqToHom e = (M.inclusion n).map g

end CompressorRelativeData

end CountingEndgame
end GroupApproximation
