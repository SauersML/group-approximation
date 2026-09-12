import GroupApproximation.KunThom.CompressorNormalizationAssemblyHammingSums
import GroupApproximation.KunThom.CompressorNormalizationAssemblyHammingObjects
import GroupApproximation.KunThom.ConjugationFailureVanishing

/-!
# Step 9 over cluster frames: the Hamming estimate for transported bisections

`CompressorNormalizationAssembly.seqNormalizes_distinguished_of_guardedSteps` leaves the
step 9 wiring `hhamming` open.  For a cluster frame with vanishing threshold, relative
data `M` of a compressor `t` and bisections `a`, `b` with `M.Transported a b`, the patched
permutation of `b` must be close to the conjugate of the patched permutation of `a` by
`A(t)`.  This is the last Hamming estimate in Kun and Thom's proof of Theorem 4.1
(arXiv:2608.06222v3).

`vanishing_hammingDistance_patch_of_transported` proves it, given words for the conjugated
generators and estimate (7) for `t` with error at most three times the scale of the image.
It applies `BlockPatching.vanishing_hammingDistance_patch_conj` with:
* the retained objects `good n`: the objects covered by the lift of the transported
  bisection whose step 9 budget is at most `cheeger / 8` times their size;
* zero edit budget, since the completed labels expand at every scale;
* reference arrows `b_{π i}` transported through the bridges realized by `A(t)⁻¹`;
* the near bound of `CompressorHammingObjects`, at radius `6 · scale i`.

The budget totals are negligible by `CompressorHamming.negligible_sum_stepNineBudget`.
Both bridge totals come from `M.bridge_negligible` and `M.unmatched_negligible`.  The
conjugation totals come from `ConjugationFailureVanishing`, and the compatibility totals
from the frame.
-/

namespace GroupApproximation
namespace CompressorHamming

open CategoryTheory CompressorNormalizationAssembly CountingEndgame GroupoidPresentation
open FinitePartialBijection BlockPatching CentralizerNormalizationImprove

variable {G : Type} [Group G] {A : SoficApproximation G} {K : Type} [Group K] {ι : K →* G}
  {R : RetainedComponents A K ι}

/-- **Exceptional mass of a filtered family.**  Off a family `G₀` and its subfamily of
objects satisfying `p`, the weight is at most the weight off `G₀` plus `c` times the
total of `f` over `G₀`, provided every object of `G₀` failing `p` has weight at most
`c · f`. -/
theorem sum_compl_filter_le {I : Type*} [Fintype I] [DecidableEq I] (G₀ : Finset I)
    (w f : I → ℝ) (c : ℝ) (hc : 0 ≤ c) (hf : ∀ i, 0 ≤ f i) (p : I → Prop) [DecidablePred p]
    (hbad : ∀ i ∈ G₀, ¬ p i → w i ≤ c * f i) :
    ∑ i ∈ (G₀.filter p)ᶜ, w i ≤ ∑ i ∈ Finset.univ \ G₀, w i + c * ∑ i ∈ G₀, f i := by
  have hsub : G₀.filter p ⊆ G₀ := Finset.filter_subset _ _
  have e₁ : ∑ i ∈ Finset.univ \ G₀.filter p, w i + ∑ i ∈ G₀.filter p, w i = ∑ i, w i :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have e₂ : ∑ i ∈ Finset.univ \ G₀, w i + ∑ i ∈ G₀, w i = ∑ i, w i :=
    Finset.sum_sdiff (Finset.subset_univ _)
  have e₃ : ∑ i ∈ G₀ \ G₀.filter p, w i + ∑ i ∈ G₀.filter p, w i = ∑ i ∈ G₀, w i :=
    Finset.sum_sdiff hsub
  have hbad' : ∑ i ∈ G₀ \ G₀.filter p, w i ≤ ∑ i ∈ G₀ \ G₀.filter p, c * f i := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    obtain ⟨hiG, hinot⟩ := Finset.mem_sdiff.mp hi
    exact hbad i hiG fun hp ↦ hinot (Finset.mem_filter.mpr ⟨hiG, hp⟩)
  have hsubset : ∑ i ∈ G₀ \ G₀.filter p, c * f i ≤ ∑ i ∈ G₀, c * f i :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun i _ _ ↦ mul_nonneg hc (hf i)
  have hmul : ∑ i ∈ G₀, c * f i = c * ∑ i ∈ G₀, f i := by
    rw [Finset.mul_sum]
  rw [Finset.compl_eq_univ_sdiff]
  linarith

open Classical in
/-- **Step 9 from the covered objects.**  The assembly of
`BlockPatching.vanishing_hammingDistance_patch_conj` once the transported data is unpacked
and the step 9 budget over the objects covered by the lift is negligible. -/
theorem vanishing_hammingDistance_patch_of_good (F : ClusterFrame R)
    (hthr : Vanishing F.threshold) (t : G) (M : CompressorRelativeData t F)
    (ws : ↥R.data.generators → List ↥R.data.generators) (k : ℕ)
    (hk : ∀ s, (ws s).length ≤ k)
    (ε : ∀ n, ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj →
      ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj → ℕ)
    (h7 : ∀ (n : ℕ)
      {X Z : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj}
      (c : (F.system n).presentation.Rep X.val.1 Z.val.1)
      (θ : (F.system n).presentation.Rep
        ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1
        ((M.functor t M.mem_compressors n).F.toFunctor.obj Z).val.1),
      ((F.system n).presentation.restrict (M.matched t n : Set (F.Obj n))).ofRep
          (X := (M.functor t M.mem_compressors n).F.toFunctor.obj X)
          (Y := (M.functor t M.mem_compressors n).F.toFunctor.obj Z) θ =
        (M.functor t M.mem_compressors n).F.toFunctor.map
          (((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).ofRep
            (X := X) (Y := Z) c) →
      ((F.system n).clusterMetric.val θ).twoSidedDisagreement
        (sandwich
          ((F.embedding n).bridge (A.map n t)⁻¹ X.val.1
            ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1)
          ((F.embedding n).bridge (A.map n t)⁻¹ Z.val.1
            ((M.functor t M.mem_compressors n).F.toFunctor.obj Z).val.1)
          ((F.system n).clusterMetric.val c)) < ε n X Z)
    (hε : ∀ n X Z, ε n X Z ≤
      3 * (F.system n).scale ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1)
    (a b : ∀ n, F.Bis n)
    (S : ∀ n, Finset ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj)
    (sel : ∀ n, ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj →
      ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj)
    (hS : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) (fun n ↦
      ∑ i ∈ Finset.univ \ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        (Fintype.card ((F.embedding n).model i) : ℝ)))
    (hlift : ∀ n, ∀ X ∈ S n,
      ∃ hsel : (M.liftFunctor n).obj (sel n X) = (a n).objEquiv ((M.liftFunctor n).obj X),
        ∃ g : X ⟶ sel n X,
          (M.liftFunctor n).map g = (a n).hom ((M.liftFunctor n).obj X) ≫ eqToHom hsel.symm ∧
          ∃ e : (b n).objEquiv ((M.inclusion n).obj X) = (M.inclusion n).obj (sel n X),
            (b n).hom ((M.inclusion n).obj X) ≫ eqToHom e = (M.inclusion n).map g)
    (hbudG₀ : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        ((F.embedding n).stepNineBudget (F.arrows n (a n)) (F.arrows n (b n)) (A.map n t)
          (F.action n) ws k (M.functor t M.mem_compressors n).π i : ℝ)) :
    Vanishing fun n ↦ hammingDistance (A.model n) (F.patch n (b n))
      (A.map n t * F.patch n (a n) * (A.map n t)⁻¹) := by
  have hc : 0 < R.data.family.cheeger := R.data.family.cheeger_pos
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  refine vanishing_hammingDistance_patch_conj (fun n ↦ F.arrows n (a n))
    (fun n ↦ F.arrows n (b n)) (fun n ↦ A.map n t) (fun n ↦ F.action n)
    (fun n ↦ ((S n).image (fun X ↦ ((M.liftFunctor n).obj X).val)).filter fun i ↦
      8 * ((F.embedding n).stepNineBudget (F.arrows n (a n)) (F.arrows n (b n)) (A.map n t)
        (F.action n) ws k (M.functor t M.mem_compressors n).π i : ℝ) ≤
        R.data.family.cheeger * Fintype.card ((F.embedding n).model i))
    (fun n i ↦ sandwich
      ((F.embedding n).bridge (A.map n t)⁻¹ ((M.functor t M.mem_compressors n).π i) i)
      ((F.embedding n).bridge (A.map n t)⁻¹
        ((F.arrows n (b n)).objEquiv ((M.functor t M.mem_compressors n).π i))
        ((F.arrows n (a n)).objEquiv i))
      ((F.arrows n (b n)).arrow ((M.functor t M.mem_compressors n).π i)))
    (fun n i _ ↦ (F.embedding n).realizesOn_sandwich_bridge_inv (F.arrows n (a n))
      (F.arrows n (b n)) (A.map n t) ((M.functor t M.mem_compressors n).π i) i)
    hc (fun _ _ ↦ 0)
    (fun n i ↦ ((F.embedding n).stepNineBudget (F.arrows n (a n)) (F.arrows n (b n))
      (A.map n t) (F.action n) ws k (M.functor t M.mem_compressors n).π i : ℝ))
    (fun n i ↦ 3 * (F.system n).scale i) (fun _ _ _ ↦ le_rfl) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the completed labels expand at every positive scale
    intro n i _ m hm
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0
        simp at hm
      · exact hpos
    have h1 : HasTaggedExpansionAtScale ((F.system n).act i) R.data.family.cheeger 1 :=
      hasTaggedExpansionAtScale_of_cheeger ((restrictFrom R.data.family F.start).expands n i)
        hc le_rfl 1
    exact BlockPatching.hasTaggedExpansionAtScale_of_le (hasTaggedExpansionAtScale_mono h1 hm1)
      (by linarith) (by linarith)
  · intro n i _
    exact_mod_cast (F.embedding n).card_equivarianceDefect_le_stepNineBudget (F.arrows n (a n))
      (F.arrows n (b n)) (A.map n t) (F.action n) ws hk (M.functor t M.mem_compressors n).π i
  · intro n i hi
    obtain ⟨hG₀, _⟩ := Finset.mem_filter.mp hi
    obtain ⟨X, hXS, hXi⟩ := Finset.mem_image.mp hG₀
    obtain ⟨hsel, g, hg₁, e, hg₂⟩ := hlift n X hXS
    subst hXi
    exact card_disagreement_lt_of_transported M n (ε n) (h7 n) (hε n) (a n) (b n) X (sel n X)
      hsel g hg₁ e hg₂
  · intro n i hi
    obtain ⟨_, hbud⟩ := Finset.mem_filter.mp hi
    have hs18 : 18 * (F.system n).scale i ≤ Fintype.card ((F.system n).model i) := by
      have h := (F.system n).scale_eq i
      omega
    have hl := (F.system n).scale_large i
    have hs18R : (18 : ℝ) * ((F.system n).scale i : ℝ) ≤
        Fintype.card ((F.embedding n).model i) := by
      exact_mod_cast hs18
    have hl20 : (20 : ℝ) ≤ ((F.system n).scale i : ℝ) := by
      exact_mod_cast hl
    have hcast : ((3 * (F.system n).scale i : ℕ) : ℝ) = 3 * ((F.system n).scale i : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    have hdiv : (2 * 0 + 4 * ((F.embedding n).stepNineBudget (F.arrows n (a n))
        (F.arrows n (b n)) (A.map n t) (F.action n) ws k (M.functor t M.mem_compressors n).π
          i : ℝ)) / R.data.family.cheeger ≤
        (Fintype.card ((F.embedding n).model i) : ℝ) / 2 := by
      rw [div_le_iff₀ hc]
      linarith
    show (2 * ((3 * (F.system n).scale i : ℕ) : ℝ)) +
        (2 * 0 + 4 * ((F.embedding n).stepNineBudget (F.arrows n (a n)) (F.arrows n (b n))
          (A.map n t) (F.action n) ws k (M.functor t M.mem_compressors n).π i : ℝ)) /
            R.data.family.cheeger + 1 ≤
      Fintype.card ((F.embedding n).model i)
    linarith
  · refine Negligible.mono_nonneg hN (fun _ ↦ Nat.cast_nonneg _) (fun n ↦ ?_)
      (F.uncovered_negligible.add
        (negligible_threshold_mul_card F.threshold (fun n ↦ (F.threshold_pos n).le) hthr 1))
    have h₁ := (F.arrows n (a n)).card_compl_domain_le
    have h₂ : ∑ C, ((F.arrows n (a n)).arrow C).sourceDefect ≤
        ∑ C, (((F.arrows n (a n)).arrow C).equivarianceDefect ((F.action n).blockAct C)
          ((F.action n).blockAct ((F.arrows n (a n)).objEquiv C))).card :=
      Finset.sum_le_sum fun C _ ↦ BlockPatching.sourceDefect_le_card_equivarianceDefect _ _ _
    have h₃ := (F.arrows n (a n)).sum_card_equivarianceDefect_le_of_candidates (F.action n)
      (F.threshold_pos n).le (fun C ↦ min ((F.system n).scale C)
        ((F.system n).scale ((F.arrows n (a n)).objEquiv C)))
      (fun C ↦ (F.system n).size_min_left C _) (fun C ↦ F.arrows_isClusterCandidate n (a n) C)
    have h₄ : (((Finset.univ \ (F.arrows n (a n)).domain).card : ℕ) : ℝ) ≤
        ((F.embedding n).uncovered.card : ℝ) +
          ((∑ C, (((F.arrows n (a n)).arrow C).equivarianceDefect ((F.action n).blockAct C)
            ((F.action n).blockAct ((F.arrows n (a n)).objEquiv C))).card : ℕ) : ℝ) := by
      exact_mod_cast h₁.trans (Nat.add_le_add_left h₂ _)
    beta_reduce
    linarith
  · refine Negligible.mono_nonneg hN (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (fun n ↦ sum_compl_filter_le ((S n).image (fun X ↦ ((M.liftFunctor n).obj X).val))
        (fun i ↦ (Fintype.card ((F.embedding n).model i) : ℝ))
        (fun i ↦ ((F.embedding n).stepNineBudget (F.arrows n (a n)) (F.arrows n (b n))
          (A.map n t) (F.action n) ws k (M.functor t M.mem_compressors n).π i : ℝ))
        (8 / R.data.family.cheeger) (div_nonneg (by norm_num) hc.le)
        (fun _ ↦ Nat.cast_nonneg _)
        (fun i ↦ 8 * ((F.embedding n).stepNineBudget (F.arrows n (a n)) (F.arrows n (b n))
          (A.map n t) (F.action n) ws k (M.functor t M.mem_compressors n).π i : ℝ) ≤
          R.data.family.cheeger * Fintype.card ((F.embedding n).model i))
        fun i _ hnot ↦ ?_)
      (hS.add (hbudG₀.const_mul (8 / R.data.family.cheeger)))
    beta_reduce at hnot ⊢
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    push Not at hnot
    linarith
  · exact Negligible.zero.congr fun n ↦ by simp
  · exact Negligible.mono_nonneg hN (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (fun n ↦ Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun _ _ _ ↦ Nat.cast_nonneg _) hbudG₀

open Classical in
/-- **Step 9 for transported bisections.**  Let `F` be a cluster frame with vanishing
threshold, `M` relative data of a compressor `t`, `ws` words of length at most `k` for the
conjugated generators, and `ε` the error of estimate (7) for `t`, at most three times the
scale of the image.  If `M.Transported a b`, the patched permutations of `b` and the
conjugates of the patched permutations of `a` by `A(t)` have vanishing Hamming distance. -/
theorem vanishing_hammingDistance_patch_of_transported (F : ClusterFrame R)
    (hthr : Vanishing F.threshold) (t : G) (M : CompressorRelativeData t F)
    (ws : ↥R.data.generators → List ↥R.data.generators) (k : ℕ)
    (hk : ∀ s, (ws s).length ≤ k)
    (hws : ∀ s, ((ws s).map fun l ↦ ι (l : K)).prod = t * ι (s : K) * t⁻¹)
    (ε : ∀ n, ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj →
      ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj → ℕ)
    (h7 : ∀ (n : ℕ)
      {X Z : ((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).Obj}
      (c : (F.system n).presentation.Rep X.val.1 Z.val.1)
      (θ : (F.system n).presentation.Rep
        ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1
        ((M.functor t M.mem_compressors n).F.toFunctor.obj Z).val.1),
      ((F.system n).presentation.restrict (M.matched t n : Set (F.Obj n))).ofRep
          (X := (M.functor t M.mem_compressors n).F.toFunctor.obj X)
          (Y := (M.functor t M.mem_compressors n).F.toFunctor.obj Z) θ =
        (M.functor t M.mem_compressors n).F.toFunctor.map
          (((F.system n).presentation.restrict (M.retained t n : Set (F.Obj n))).ofRep
            (X := X) (Y := Z) c) →
      ((F.system n).clusterMetric.val θ).twoSidedDisagreement
        (sandwich
          ((F.embedding n).bridge (A.map n t)⁻¹ X.val.1
            ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1)
          ((F.embedding n).bridge (A.map n t)⁻¹ Z.val.1
            ((M.functor t M.mem_compressors n).F.toFunctor.obj Z).val.1)
          ((F.system n).clusterMetric.val c)) < ε n X Z)
    (hε : ∀ n X Z, ε n X Z ≤
      3 * (F.system n).scale ((M.functor t M.mem_compressors n).F.toFunctor.obj X).val.1)
    (a b : ∀ n, F.Bis n) (htr : M.Transported a b) :
    Vanishing fun n ↦ hammingDistance (A.model n) (F.patch n (b n))
      (A.map n t * F.patch n (a n) * (A.map n t)⁻¹) := by
  obtain ⟨S, sel, hS, hlift⟩ := htr
  have hc : 0 < R.data.family.cheeger := R.data.family.cheeger_pos
  have hN : ∀ n, (0 : ℝ) ≤ Fintype.card (A.model n) := fun n ↦ Nat.cast_nonneg _
  -- objects covered by the lift, and their inclusion in the matched objects
  have hG₀sub : ∀ n, (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val) ⊆ M.matched t n := by
    intro n i hi
    obtain ⟨X, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_coe.mp ((M.functor t M.mem_compressors n).F.obj X.val).2
  have hπ : ∀ n, Set.InjOn (M.functor t M.mem_compressors n).π
      ((S n).image (fun X ↦ ((M.liftFunctor n).obj X).val)) := fun n ↦
    (M.functor t M.mem_compressors n).injOn.mono fun i hi ↦
      Finset.mem_coe.mpr (hG₀sub n (Finset.mem_coe.mp hi))
  -- the first bridge total
  have hbridge : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        (((F.embedding n).bridge (A.map n t)⁻¹ ((M.functor t M.mem_compressors n).π i)
          i).targetDefect : ℝ) := by
    refine Negligible.mono_nonneg hN (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (fun n ↦ ?_) (M.bridge_negligible t M.mem_compressors)
    calc ∑ i ∈ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
          (((F.embedding n).bridge (A.map n t)⁻¹ ((M.functor t M.mem_compressors n).π i)
            i).targetDefect : ℝ)
        = ∑ i ∈ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
          (((F.embedding n).bridge (A.map n t) i
            ((M.functor t M.mem_compressors n).π i)).sourceDefect : ℝ) :=
          Finset.sum_congr rfl fun i _ ↦ by
            rw [RelativeFunctorEstimate.targetDefect_bridge_inv]
      _ ≤ ∑ i ∈ M.matched t n, (((F.embedding n).bridge (A.map n t) i
            ((M.functor t M.mem_compressors n).π i)).sourceDefect : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (hG₀sub n) fun _ _ _ ↦ Nat.cast_nonneg _
  -- the second bridge total, through the image blocks of the transported bisection
  have hbridge' : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        (((F.embedding n).bridge (A.map n t)⁻¹
          ((F.arrows n (b n)).objEquiv ((M.functor t M.mem_compressors n).π i))
          ((F.arrows n (a n)).objEquiv i)).sourceDefect : ℝ) := by
    refine Negligible.mono_nonneg hN (fun _ ↦ Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
      (fun n ↦ ?_) ((M.bridge_negligible t M.mem_compressors).add
        (M.unmatched_negligible t M.mem_compressors))
    have hfacts : ∀ i ∈ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        (F.arrows n (b n)).objEquiv ((M.functor t M.mem_compressors n).π i) =
          (M.functor t M.mem_compressors n).π ((F.arrows n (a n)).objEquiv i) ∧
        (F.arrows n (a n)).objEquiv i ∈ M.matched t n := by
      intro i hi
      obtain ⟨X, hXS, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨hsel, _, _, e, _⟩ := hlift n X hXS
      exact transported_objEquiv M a b n X (sel n X) hsel e
    have hsum : ∑ i ∈ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        (((F.embedding n).bridge (A.map n t)⁻¹
          ((F.arrows n (b n)).objEquiv ((M.functor t M.mem_compressors n).π i))
          ((F.arrows n (a n)).objEquiv i)).sourceDefect : ℝ) =
        ∑ j ∈ ((S n).image (fun X ↦ ((M.liftFunctor n).obj X).val)).image
          (F.arrows n (a n)).objEquiv,
          (((F.embedding n).bridge (A.map n t) j
            ((M.functor t M.mem_compressors n).π j)).targetDefect : ℝ) := by
      rw [Finset.sum_image fun x _ y _ hxy ↦ (F.arrows n (a n)).objEquiv.injective hxy]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [(hfacts i hi).1, RelativeFunctorEstimate.sourceDefect_bridge_inv]
    have hsub : ((S n).image (fun X ↦ ((M.liftFunctor n).obj X).val)).image
        (F.arrows n (a n)).objEquiv ⊆ M.matched t n := by
      intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact (hfacts i hi).2
    have hle₁ : ∑ j ∈ ((S n).image (fun X ↦ ((M.liftFunctor n).obj X).val)).image
          (F.arrows n (a n)).objEquiv,
          (((F.embedding n).bridge (A.map n t) j
            ((M.functor t M.mem_compressors n).π j)).targetDefect : ℝ) ≤
        ∑ j ∈ M.matched t n, (((F.embedding n).bridge (A.map n t) j
          ((M.functor t M.mem_compressors n).π j)).targetDefect : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ Nat.cast_nonneg _
    have hle₂ : ((∑ j ∈ M.matched t n, ((F.embedding n).bridge (A.map n t) j
          ((M.functor t M.mem_compressors n).π j)).targetDefect : ℕ) : ℝ) ≤
        ((∑ j ∈ M.matched t n, ((F.embedding n).bridge (A.map n t) j
          ((M.functor t M.mem_compressors n).π j)).sourceDefect +
          ∑ j ∈ Finset.univ \ M.matched t n, Fintype.card ((F.embedding n).model j) : ℕ) :
            ℝ) := by
      exact_mod_cast sum_targetDefect_bridge_le (F.embedding n) (A.map n t)
        (M.functor t M.mem_compressors n).π (M.matched t n)
        (M.functor t M.mem_compressors n).injOn
    push_cast at hle₂
    linarith
  -- the retained budget over the covered objects
  have hbudG₀ : Negligible (fun n ↦ (Fintype.card (A.model n) : ℝ)) fun n ↦
      ∑ i ∈ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val),
        ((F.embedding n).stepNineBudget (F.arrows n (a n)) (F.arrows n (b n)) (A.map n t)
          (F.action n) ws k (M.functor t M.mem_compressors n).π i : ℝ) :=
    negligible_sum_stepNineBudget (fun n ↦ F.arrows n (a n)) (fun n ↦ F.arrows n (b n))
      (fun n ↦ A.map n t) (fun n ↦ F.action n) ws k hk
      (fun n ↦ (M.functor t M.mem_compressors n).π)
      (fun n ↦ (S n).image (fun X ↦ ((M.liftFunctor n).obj X).val)) hπ
      F.threshold (fun n ↦ (F.threshold_pos n).le) hthr
      (fun n C ↦ min ((F.system n).scale C) ((F.system n).scale
        ((F.arrows n (a n)).objEquiv C)))
      (fun n C ↦ min ((F.system n).scale C) ((F.system n).scale
        ((F.arrows n (b n)).objEquiv C)))
      (fun n C ↦ (F.system n).size_min_left C _) (fun n C ↦ (F.system n).size_min_left C _)
      (fun n C ↦ F.arrows_isClusterCandidate n (a n) C)
      (fun n C ↦ F.arrows_isClusterCandidate n (b n) C)
      hbridge hbridge' (fun s ↦ F.compat_negligible s)
      (ConjugationFailureVanishing.negligible_sum_card_conjFailure A
        (fun l : ↥R.data.generators ↦ ι (l : K)) ws t hws (fun n ↦ F.embedding n)
        (fun n ↦ F.action n) fun _ _ ↦ rfl)
      (ConjugationFailureVanishing.negligible_sum_card_conjFailure_inv A
        (fun l : ↥R.data.generators ↦ ι (l : K)) ws t hws (fun n ↦ F.embedding n)
        (fun n ↦ F.action n) fun _ _ ↦ rfl)
  exact vanishing_hammingDistance_patch_of_good F hthr t M ws k hk ε h7 hε a b S sel hS hlift
    hbudG₀

end CompressorHamming
end GroupApproximation
