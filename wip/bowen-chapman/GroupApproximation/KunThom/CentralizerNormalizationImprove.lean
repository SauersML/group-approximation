import GroupApproximation.KunThom.CentralizerNormalizationSumApproximation
import GroupApproximation.KunThom.CentralizerNormalizationParameters
import GroupApproximation.KunThom.KunThomRounding
import GroupApproximation.Kun.KunFiniteMarkov

/-!
# Uniform improvement of cluster candidates on expander components

A `ComponentFamily` is a sequence of finite families of component models, each
carrying approximate actions of a Kazhdan group `K` with an exact directed
Cheeger bound for the labels of a finite set `T`, sizes tending to infinity,
local multiplicativity and injective labels.  An object `i` at index `n` has
cluster scale `|model n i| / 18`.

`eventually_improveCloseAt` proves, for fixed improvement parameters, that
eventually every composite `f.trans g` of two cluster candidates at threshold
`η` has an improving candidate at the scale of its source object, within
`20000 ζ |model|`.  The proof is by contradiction.  A sequence of
counterexamples, one per index, packs into one multiplicative approximation on
the unions of source and target components.  The proved Kun--Thom relation
improvement (`KunThomRounding.exists_pairProduct_relation_eventually`) then
supplies relations near the swap graphs with small boundary, and the finite
repair step (`CentralizerNormalizationCrossingRepair`) turns them into
improving candidates.

`exists_joint_improvement` chooses the threshold and distance along a
diagonal of parameter levels.  Both tend to zero, and the threshold dominates
any prescribed vanishing error sequence.
-/

namespace GroupApproximation
namespace CentralizerNormalizationImprove

open Filter
open scoped Topology symmDiff
open AlmostAutomorphism
open KazhdanImprovement
open FinitePartialBijection
open CentralizerNormalizationCrossingRepair
open CentralizerNormalizationSumApproximation
open CentralizerNormalizationParameters
open KunThomRounding
open KazhdanGNS

/-! ### Candidate numerics -/

theorem card_mul_sourceDefect_lt_of_candidate {L : Type*} [Fintype L] [DecidableEq L]
    {Y Z : FiniteModel} {actY : L → Equiv.Perm Y} {actZ : L → Equiv.Perm Z}
    {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m) :
    (Fintype.card L : ℝ) * f.sourceDefect < h * m / 2 := by
  have h1 := card_mul_sourceDefect_le_card_equivarianceDefect f actY actZ
  have h1r : (Fintype.card L : ℝ) * (f.sourceDefect : ℝ) ≤
      ((f.equivarianceDefect actY actZ).card : ℝ) := by
    exact_mod_cast h1
  exact h1r.trans_lt hf.forwardSmall

theorem card_mul_targetDefect_lt_of_candidate {L : Type*} [Fintype L] [DecidableEq L]
    {Y Z : FiniteModel} {actY : L → Equiv.Perm Y} {actZ : L → Equiv.Perm Z}
    {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m) :
    (Fintype.card L : ℝ) * f.targetDefect < h * m / 2 := by
  have h1 := card_mul_targetDefect_le_card_symm_equivarianceDefect f actY actZ
  have h1r : (Fintype.card L : ℝ) * (f.targetDefect : ℝ) ≤
      ((f.symm.equivarianceDefect actZ actY).card : ℝ) := by
    exact_mod_cast h1
  exact h1r.trans_lt hf.backwardSmall

/-- A candidate below a tiny threshold misses at most a hundredth of its scale. -/
theorem hundred_mul_defects_le_of_candidate {L : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] {Y Z : FiniteModel} {actY : L → Equiv.Perm Y}
    {actZ : L → Equiv.Perm Z} {h : ℝ} {m : ℕ} {f : FinitePartialBijection Y Z}
    (hf : f.IsClusterCandidate actY actZ h m) (hh : h ≤ 1 / 100000) :
    100 * f.sourceDefect ≤ m ∧ 100 * f.targetDefect ≤ m := by
  have hL : (1 : ℝ) ≤ Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hs := card_mul_sourceDefect_lt_of_candidate hf
  have ht := card_mul_targetDefect_lt_of_candidate hf
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hsd0 : (0 : ℝ) ≤ f.sourceDefect := by positivity
  have htd0 : (0 : ℝ) ≤ f.targetDefect := by positivity
  have hhm : h * m ≤ m / 100000 := by nlinarith
  refine ⟨?_, ?_⟩
  · have hsd : (f.sourceDefect : ℝ) ≤ Fintype.card L * f.sourceDefect := by nlinarith
    have hreal : (100 * f.sourceDefect : ℝ) ≤ m := by linarith
    exact_mod_cast hreal
  · have htd : (f.targetDefect : ℝ) ≤ Fintype.card L * f.targetDefect := by nlinarith
    have hreal : (100 * f.targetDefect : ℝ) ≤ m := by linarith
    exact_mod_cast hreal

theorem card_target_le_card_source_add {Y Z : FiniteModel}
    (f : FinitePartialBijection Y Z) :
    Fintype.card Z ≤ Fintype.card Y + f.targetDefect := by
  have hst := f.card_source_eq_card_target
  have hs : f.source.card ≤ Fintype.card Y := Finset.card_le_univ _
  have ht : f.target.card ≤ Fintype.card Z := Finset.card_le_univ _
  unfold targetDefect
  omega

theorem card_source_le_card_target_add {Y Z : FiniteModel}
    (f : FinitePartialBijection Y Z) :
    Fintype.card Y ≤ Fintype.card Z + f.sourceDefect := by
  have hst := f.card_source_eq_card_target
  have hs : f.source.card ≤ Fintype.card Y := Finset.card_le_univ _
  have ht : f.target.card ≤ Fintype.card Z := Finset.card_le_univ _
  unfold sourceDefect
  omega

/-! ### Component families -/

/-- Finite families of expander component models with approximate actions. -/
structure ComponentFamily (K : Type) [Group K] (T : Finset K) where
  index : ℕ → Type
  model : ∀ n, index n → FiniteModel
  act : ∀ n (i : index n), K → Equiv.Perm (model n i)
  cheeger : ℝ
  cheeger_pos : 0 < cheeger
  expands : ∀ n (i : index n),
    DirectedCoarea.HasCheegerLowerBound (model n i) (T.image (act n i)) cheeger
  size_tendsTo : ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ i : index n,
    M ≤ Fintype.card (model n i)
  locallyMultiplicative : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    ∀ i : index n,
      hammingDistance (model n i) (act n i (g * h)) (act n i g * act n i h) < ε
  labelsInjective : ∃ N : ℕ, ∀ n ≥ N, ∀ i : index n,
    Set.InjOn (act n i) (T : Set K)

namespace ComponentFamily

variable {K : Type} [Group K] {T : Finset K} (F : ComponentFamily K T)

/-- The generator tags acting on an object. -/
def tags (n : ℕ) (i : F.index n) : T → Equiv.Perm (F.model n i) :=
  fun t ↦ F.act n i t.1

/-- The cluster scale of an object. -/
def scale (n : ℕ) (i : F.index n) : ℕ := Fintype.card (F.model n i) / 18

/-- The boundary factor of the improvement parameters. -/
noncomputable def repairFactor : ℝ :=
  F.cheeger ^ 2 / (360 * (2 + F.cheeger) * T.card * (F.cheeger + 7 * T.card))

theorem repairFactor_pos (hone : (1 : K) ∈ T) : 0 < F.repairFactor := by
  have hc := F.cheeger_pos
  have hT : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.mpr ⟨1, hone⟩
  unfold repairFactor
  positivity

open Classical in
theorem univ_image_tags (n : ℕ) (i : F.index n) :
    Finset.univ.image (F.tags n i) = T.image (F.act n i) := by
  ext σ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, tags]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.1, t.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

open Classical in
/-- Improvement of composites of candidates at index `n`, threshold `h'` and
distance factor `d`, each arrow at the scale of its source object. -/
def ImproveCloseAt (h' d : ℝ) (n : ℕ) : Prop :=
  ∀ (i j l : F.index n)
    (f : FinitePartialBijection (F.model n i) (F.model n j)),
    f.IsClusterCandidate (F.tags n i) (F.tags n j) h' (F.scale n i) →
    ∀ g : FinitePartialBijection (F.model n j) (F.model n l),
    g.IsClusterCandidate (F.tags n j) (F.tags n l) h' (F.scale n j) →
    ∃ r : FinitePartialBijection (F.model n i) (F.model n l),
      r.IsClusterCandidate (F.tags n i) (F.tags n l) h' (F.scale n i) ∧
        r.twoSidedDisagreement (f.trans g) < 2 * F.scale n i ∧
        (r.twoSidedDisagreement (f.trans g) : ℝ) ≤ d * Fintype.card (F.model n i)

open Classical in
/-- A counterexample to improvement at index `n`. -/
structure BadTriple (h' d : ℝ) (n : ℕ) where
  i : F.index n
  j : F.index n
  l : F.index n
  f : FinitePartialBijection (F.model n i) (F.model n j)
  hf : f.IsClusterCandidate (F.tags n i) (F.tags n j) h' (F.scale n i)
  g : FinitePartialBijection (F.model n j) (F.model n l)
  hg : g.IsClusterCandidate (F.tags n j) (F.tags n l) h' (F.scale n j)
  noImprove : ∀ r : FinitePartialBijection (F.model n i) (F.model n l),
    ¬ (r.IsClusterCandidate (F.tags n i) (F.tags n l) h' (F.scale n i) ∧
      r.twoSidedDisagreement (f.trans g) < 2 * F.scale n i ∧
      (r.twoSidedDisagreement (f.trans g) : ℝ) ≤ d * Fintype.card (F.model n i))

theorem improveCloseAt_of_not_nonempty {h' d : ℝ} {n : ℕ}
    (h : ¬ Nonempty (F.BadTriple h' d n)) : F.ImproveCloseAt h' d n := by
  classical
  intro i j l f hf g hg
  by_contra hno
  exact h ⟨{ i := i, j := j, l := l, f := f, hf := hf, g := g, hg := hg,
    noImprove := fun r hr ↦ hno ⟨r, hr⟩ }⟩

open Classical in
/-- **Improvement at fixed parameters.** -/
theorem eventually_improveCloseAt
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ) (hQT : Q ⊆ T)
    (hone : (1 : K) ∈ T) (hκone : κ ≤ 1)
    {k : ℕ} {η δ ζ : ℝ} (hk : 0 < k) (hη : 0 < η) (hδ : 0 < δ)
    (hζ : ζ ≤ 1 / 100000) (hηζ : η < ζ) (hkη : (k : ℝ) ^ 2 * η < ζ)
    (hnumerical : 16 * (T.card : ℝ) ^ 4 *
        (16 * (1 - κ ^ 2 / (4 * T.card)) ^ (2 * k) * (T.card : ℝ)⁻¹ * η + δ) <
      (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
        (F.repairFactor * η) ^ 4) :
    ∃ N : ℕ, ∀ n ≥ N, F.ImproveCloseAt η (20000 * ζ) n := by
  classical
  by_contra hcontra
  have hbad : ∀ N : ℕ, ∃ n, N ≤ n ∧ Nonempty (F.BadTriple η (20000 * ζ) n) := by
    intro N
    by_contra hN
    exact hcontra ⟨N, fun n hn ↦
      F.improveCloseAt_of_not_nonempty fun hne ↦ hN ⟨n, hn, hne⟩⟩
  choose seq hseq hbadN using hbad
  let bad : ∀ N, F.BadTriple η (20000 * ζ) (seq N) := fun N ↦ Classical.choice (hbadN N)
  haveI : Nonempty T := ⟨⟨1, hone⟩⟩
  have hc := F.cheeger_pos
  have hηsmall : η ≤ 1 / 100000 := by linarith
  have hsT : (1 : ℝ) ≤ Fintype.card T := by exact_mod_cast Fintype.card_pos
  have hTc : (1 : ℝ) ≤ T.card := by
    have h := Finset.card_pos.mpr ⟨(1 : K), hone⟩
    exact_mod_cast h
  -- Natural-number facts about each counterexample.
  have hscaleX : ∀ N, 1 ≤ F.scale (seq N) (bad N).i := by
    intro N
    have h := (bad N).hf.selfSmall
    omega
  have hsizes : ∀ N,
      18 * F.scale (seq N) (bad N).i ≤ Fintype.card (F.model (seq N) (bad N).i) ∧
      Fintype.card (F.model (seq N) (bad N).i) +
          Fintype.card (F.model (seq N) (bad N).l) ≤ 90 * F.scale (seq N) (bad N).i ∧
      17 * F.scale (seq N) (bad N).i ≤ Fintype.card (F.model (seq N) (bad N).l) ∧
      F.scale (seq N) (bad N).j ≤ 2 * F.scale (seq N) (bad N).i := by
    intro N
    have hX := hscaleX N
    have hfd := hundred_mul_defects_le_of_candidate (bad N).hf hηsmall
    have hgd := hundred_mul_defects_le_of_candidate (bad N).hg hηsmall
    have hY1 := card_target_le_card_source_add (bad N).f
    have hY2 := card_source_le_card_target_add (bad N).f
    have hZ1 := card_target_le_card_source_add (bad N).g
    have hZ2 := card_source_le_card_target_add (bad N).g
    have hmX : F.scale (seq N) (bad N).i =
        Fintype.card (F.model (seq N) (bad N).i) / 18 := rfl
    have hmY : F.scale (seq N) (bad N).j =
        Fintype.card (F.model (seq N) (bad N).j) / 18 := rfl
    omega
  -- The combined approximation on the unions of source and target components.
  let modelX : ℕ → FiniteModel := fun N ↦ F.model (seq N) (bad N).i
  let modelZ : ℕ → FiniteModel := fun N ↦ F.model (seq N) (bad N).l
  let actX : ∀ N, K → Equiv.Perm (modelX N) := fun N ↦ F.act (seq N) (bad N).i
  let actZ : ∀ N, K → Equiv.Perm (modelZ N) := fun N ↦ F.act (seq N) (bad N).l
  have hposX : ∀ N, 0 < Fintype.card (modelX N) := by
    intro N
    have h := (hsizes N).1
    have hX := hscaleX N
    show 0 < Fintype.card (F.model (seq N) (bad N).i)
    omega
  have hposZ : ∀ N, 0 < Fintype.card (modelZ N) := by
    intro N
    have h := (hsizes N).2.2.1
    have hX := hscaleX N
    show 0 < Fintype.card (F.model (seq N) (bad N).l)
    omega
  have hcard : ∀ M : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, M ≤ Fintype.card (modelX N) := by
    intro M
    obtain ⟨N₀, hN₀⟩ := F.size_tendsTo M
    exact ⟨N₀, fun N hN ↦ hN₀ (seq N) (hN.trans (hseq N)) (bad N).i⟩
  have hmulX : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      hammingDistance (modelX N) (actX N (g * h)) (actX N g * actX N h) < ε := by
    intro g h ε hε
    obtain ⟨N₀, hN₀⟩ := F.locallyMultiplicative g h ε hε
    exact ⟨N₀, fun N hN ↦ hN₀ (seq N) (hN.trans (hseq N)) (bad N).i⟩
  have hmulZ : ∀ (g h : K) (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
      hammingDistance (modelZ N) (actZ N (g * h)) (actZ N g * actZ N h) < ε := by
    intro g h ε hε
    obtain ⟨N₀, hN₀⟩ := F.locallyMultiplicative g h ε hε
    exact ⟨N₀, fun N hN ↦ hN₀ (seq N) (hN.trans (hseq N)) (bad N).l⟩
  let A := sumApproximation modelX modelZ actX actZ hposX hposZ hcard hmulX hmulZ
  have hβ : 0 < F.repairFactor * η := mul_pos (F.repairFactor_pos hone) hη
  obtain ⟨N₁, hN₁⟩ := exists_pairProduct_relation_eventually hQ T hQT hone hκone A k hk
    hδ hβ hnumerical
  obtain ⟨N₂, hN₂⟩ := F.labelsInjective
  let N : ℕ := max N₁ N₂
  have hN1 : N₁ ≤ N := le_max_left _ _
  have hNseq : N₂ ≤ seq N := (le_max_right _ _).trans (hseq N)
  have hinj : Set.InjOn (fun x : K ↦ A.map N (x, (1 : Unit))) (T : Set K) :=
    injOn_sumApproximation_map modelX modelZ actX actZ hposX hposZ hcard hmulX hmulZ T N
      (hN₂ (seq N) hNseq (bad N).i)
  have hcardSum : Fintype.card (sumModel (modelX N) (modelZ N)) =
      Fintype.card (modelX N) + Fintype.card (modelZ N) := Fintype.card_sum
  have hcardPos : 0 < Fintype.card (A.model N) := by
    show 0 < Fintype.card (sumModel (modelX N) (modelZ N))
    rw [hcardSum]
    have := hposX N
    omega
  have hlabels : multiplicativeProductLabels A N T =
      Finset.univ.image
        (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)) :=
    multiplicativeProductLabels_sumApproximation modelX modelZ actX actZ hposX hposZ
      hcard hmulX hmulZ T N
  -- Real-number facts at the chosen index.
  have hsz := hsizes N
  have hmXr : (1 : ℝ) ≤ F.scale (seq N) (bad N).i := by exact_mod_cast hscaleX N
  have hWr : (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) ≤
      90 * (F.scale (seq N) (bad N).i : ℝ) := by
    have h : Fintype.card (sumModel (modelX N) (modelZ N)) ≤
        90 * F.scale (seq N) (bad N).i := by
      rw [hcardSum]
      exact hsz.2.1
    exact_mod_cast h
  have hWlow : 18 * (F.scale (seq N) (bad N).i : ℝ) ≤
      (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) := by
    have h : 18 * F.scale (seq N) (bad N).i ≤
        Fintype.card (sumModel (modelX N) (modelZ N)) := by
      rw [hcardSum]
      have := hsz.1
      show 18 * F.scale (seq N) (bad N).i ≤
        Fintype.card (F.model (seq N) (bad N).i) +
          Fintype.card (F.model (seq N) (bad N).l)
      omega
    exact_mod_cast h
  have hmYr : (F.scale (seq N) (bad N).j : ℝ) ≤ 2 * (F.scale (seq N) (bad N).i : ℝ) := by
    exact_mod_cast hsz.2.2.2
  -- Goodness of the swap encoding of the composite.
  have hfF := (bad N).hf.forwardSmall
  have hfB := (bad N).hf.backwardSmall
  have hgF := (bad N).hg.forwardSmall
  have hgB := (bad N).hg.backwardSmall
  have hsum4 :
      (((bad N).f.equivarianceDefect (F.tags (seq N) (bad N).i)
          (F.tags (seq N) (bad N).j)).card : ℝ) +
        (((bad N).g.equivarianceDefect (F.tags (seq N) (bad N).j)
          (F.tags (seq N) (bad N).l)).card : ℝ) +
        ((((bad N).g.symm.equivarianceDefect (F.tags (seq N) (bad N).l)
          (F.tags (seq N) (bad N).j)).card : ℝ) +
          (((bad N).f.symm.equivarianceDefect (F.tags (seq N) (bad N).j)
            (F.tags (seq N) (bad N).i)).card : ℝ)) <
        3 * η * F.scale (seq N) (bad N).i := by
    nlinarith
  have harcs := card_badArcs_swap_trans_le (F.tags (seq N) (bad N).i)
    (F.tags (seq N) (bad N).j) (F.tags (seq N) (bad N).l) (bad N).f (bad N).g
  have harcsInv := card_badArcs_swap_trans_inv_le (F.tags (seq N) (bad N).i)
    (F.tags (seq N) (bad N).j) (F.tags (seq N) (bad N).l) (bad N).f (bad N).g
  have ha : IsEpsilonGood (A.model N) (multiplicativeProductLabels A N T) η
      ((bad N).f.trans (bad N).g).swapPerm := by
    rw [hlabels]
    refine ⟨?_, ?_⟩
    · show ((badArcs (sumModel (modelX N) (modelZ N))
          (Finset.univ.image
            (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
          ((bad N).f.trans (bad N).g).swapPerm).card : ℝ) <
        η * (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ)
      have hcast :
          ((badArcs (sumModel (modelX N) (modelZ N))
            (Finset.univ.image
              (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
            ((bad N).f.trans (bad N).g).swapPerm).card : ℝ) ≤
          (((bad N).f.equivarianceDefect (F.tags (seq N) (bad N).i)
              (F.tags (seq N) (bad N).j)).card : ℝ) +
            (((bad N).g.equivarianceDefect (F.tags (seq N) (bad N).j)
              (F.tags (seq N) (bad N).l)).card : ℝ) +
            ((((bad N).g.symm.equivarianceDefect (F.tags (seq N) (bad N).l)
              (F.tags (seq N) (bad N).j)).card : ℝ) +
              (((bad N).f.symm.equivarianceDefect (F.tags (seq N) (bad N).j)
                (F.tags (seq N) (bad N).i)).card : ℝ)) := by
        exact_mod_cast harcs
      nlinarith
    · show ((badArcs (sumModel (modelX N) (modelZ N))
          (Finset.univ.image
            (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
          ((bad N).f.trans (bad N).g).swapPerm⁻¹).card : ℝ) <
        η * (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ)
      have hcast :
          ((badArcs (sumModel (modelX N) (modelZ N))
            (Finset.univ.image
              (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
            ((bad N).f.trans (bad N).g).swapPerm⁻¹).card : ℝ) ≤
          (((bad N).f.equivarianceDefect (F.tags (seq N) (bad N).i)
              (F.tags (seq N) (bad N).j)).card : ℝ) +
            (((bad N).g.equivarianceDefect (F.tags (seq N) (bad N).j)
              (F.tags (seq N) (bad N).l)).card : ℝ) +
            ((((bad N).g.symm.equivarianceDefect (F.tags (seq N) (bad N).l)
              (F.tags (seq N) (bad N).j)).card : ℝ) +
              (((bad N).f.symm.equivarianceDefect (F.tags (seq N) (bad N).j)
                (F.tags (seq N) (bad N).i)).card : ℝ)) := by
        exact_mod_cast harcsInv
      nlinarith
  have hb : IsEpsilonGood (A.model N) (multiplicativeProductLabels A N T) η 1 :=
    isEpsilonGood_one (A.model N) _ hη hcardPos
  obtain ⟨U, hUclose, hUboundary⟩ := hN₁ N hN1 hinj hcardPos ha hb
  rw [mul_one] at hUclose
  rw [hlabels] at hUboundary
  have hUclose' :
      ((U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card : ℝ) <
        36 * (k : ℝ) ^ 2 * (T.card : ℝ)⁻¹ * η *
          (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) := hUclose
  have hUboundary' :
      ((relationBoundary (sumModel (modelX N) (modelZ N))
          (Finset.univ.image
            (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
          U).card : ℝ) <
        F.repairFactor * η * (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) :=
    hUboundary
  -- The edit count of `U` against the swap graph.
  have hEreal :
      ((U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card : ℝ) <
        3240 * ζ * F.scale (seq N) (bad N).i := by
    have hW0 : (0 : ℝ) ≤ (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) := by
      positivity
    have h1 : 36 * (k : ℝ) ^ 2 * (T.card : ℝ)⁻¹ * η *
          (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) ≤
        36 * ((k : ℝ) ^ 2 * η) *
          (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) := by
      have hEq : 36 * (k : ℝ) ^ 2 * (T.card : ℝ)⁻¹ * η *
            (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) =
          (36 * ((k : ℝ) ^ 2 * η) *
            (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ)) / T.card := by
        ring
      rw [hEq]
      exact div_le_self (by positivity) hTc
    have h2 : 36 * ((k : ℝ) ^ 2 * η) *
          (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ) ≤
        36 * ζ * (90 * (F.scale (seq N) (bad N).i : ℝ)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hkη.le (by norm_num)) hWr hW0
      positivity
    linarith
  have hE100 :
      100 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card <
        4 * F.scale (seq N) (bad N).i := by
    have hreal :
        (100 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card : ℝ) <
          4 * (F.scale (seq N) (bad N).i : ℝ) := by
      nlinarith
    exact_mod_cast hreal
  have hE :
      (permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm \ U).card +
        (U \ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card ≤
      (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card :=
    le_of_eq (card_sdiff_add_card_sdiff_eq_symmDiff U
      (permutationGraph (sumModel (modelX N) (modelZ N))
        ((bad N).f.trans (bad N).g).swapPerm))
  -- Defects of the composite.
  have hfd := hundred_mul_defects_le_of_candidate (bad N).hf hηsmall
  have hgd := hundred_mul_defects_le_of_candidate (bad N).hg hηsmall
  have hbs := sourceDefect_trans_le (bad N).f (bad N).g
  have hbt := targetDefect_trans_le (bad N).f (bad N).g
  have hsmallX :
      2 * (((bad N).f.trans (bad N).g).sourceDefect +
        3 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card) ≤
        Fintype.card (modelX N) := by
    have h := hsz.1
    have h2 := hsz.2.2.2
    show 2 * (((bad N).f.trans (bad N).g).sourceDefect +
        3 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card) ≤
        Fintype.card (F.model (seq N) (bad N).i)
    omega
  have hsmallZ :
      2 * (((bad N).f.trans (bad N).g).targetDefect +
        3 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card) ≤
        Fintype.card (modelZ N) := by
    have h := hsz.2.2.1
    have h2 := hsz.2.2.2
    show 2 * (((bad N).f.trans (bad N).g).targetDefect +
        3 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card) ≤
        Fintype.card (F.model (seq N) (bad N).l)
    omega
  have hclose :
      ((bad N).f.trans (bad N).g).sourceDefect +
          ((bad N).f.trans (bad N).g).targetDefect +
          6 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
            ((bad N).f.trans (bad N).g).swapPerm).card <
        2 * F.scale (seq N) (bad N).i := by
    have h2 := hsz.2.2.2
    have hX := hscaleX N
    omega
  -- The boundary inequality for the repair step.
  have hSWcard :
      ((Finset.univ.image
          (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l))).card : ℝ) ≤
        T.card := by
    have h : (Finset.univ.image
        (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l))).card ≤
        T.card := by
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_univ, Fintype.card_coe]
    exact_mod_cast h
  have hid : (2 + F.cheeger) * (T.card : ℝ) * (F.cheeger + 7 * T.card) * F.repairFactor =
      F.cheeger ^ 2 / 360 := by
    unfold repairFactor
    have h1 : (2 + F.cheeger) ≠ 0 := by positivity
    have h2 : (T.card : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have h3 : (F.cheeger + 7 * T.card) ≠ 0 := by positivity
    field_simp
  have hforward :
      (2 * (Fintype.card T : ℝ) + F.cheeger * Fintype.card T) *
          ((F.cheeger + 7 * (Finset.univ.image
              (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l))).card) *
            ((relationBoundary (sumModel (modelX N) (modelZ N))
              (Finset.univ.image
                (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
              U).card : ℝ)) <
        F.cheeger * F.cheeger * (η * F.scale (seq N) (bad N).i / 2) := by
    rw [Fintype.card_coe]
    have hB0 : (0 : ℝ) ≤ ((relationBoundary (sumModel (modelX N) (modelZ N))
        (Finset.univ.image
          (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
        U).card : ℝ) := by positivity
    have hcoef : (0 : ℝ) < 2 * (T.card : ℝ) + F.cheeger * T.card := by positivity
    have hpη : (0 : ℝ) ≤ F.repairFactor * η := hβ.le
    have hprod : 0 < F.cheeger ^ 2 * η * (F.scale (seq N) (bad N).i : ℝ) := by
      have := mul_pos (mul_pos (pow_pos hc 2) hη) (by linarith : (0 : ℝ) <
        (F.scale (seq N) (bad N).i : ℝ))
      linarith
    calc (2 * (T.card : ℝ) + F.cheeger * T.card) *
          ((F.cheeger + 7 * (Finset.univ.image
              (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l))).card) *
            ((relationBoundary (sumModel (modelX N) (modelZ N))
              (Finset.univ.image
                (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
              U).card : ℝ))
        ≤ (2 * (T.card : ℝ) + F.cheeger * T.card) *
          ((F.cheeger + 7 * T.card) *
            ((relationBoundary (sumModel (modelX N) (modelZ N))
              (Finset.univ.image
                (sumAction (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l)))
              U).card : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hcoef.le
          apply mul_le_mul_of_nonneg_right _ hB0
          linarith
      _ < (2 * (T.card : ℝ) + F.cheeger * T.card) *
          ((F.cheeger + 7 * T.card) *
            (F.repairFactor * η * (Fintype.card (sumModel (modelX N) (modelZ N)) : ℝ))) := by
          apply mul_lt_mul_of_pos_left _ hcoef
          exact mul_lt_mul_of_pos_left hUboundary' (by positivity)
      _ ≤ (2 * (T.card : ℝ) + F.cheeger * T.card) *
          ((F.cheeger + 7 * T.card) *
            (F.repairFactor * η * (90 * (F.scale (seq N) (bad N).i : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ hcoef.le
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hWr hpη
      _ = 90 * η * (F.scale (seq N) (bad N).i : ℝ) *
          ((2 + F.cheeger) * (T.card : ℝ) * (F.cheeger + 7 * T.card) * F.repairFactor) := by
          ring
      _ = F.cheeger ^ 2 * η * (F.scale (seq N) (bad N).i : ℝ) / 4 := by
          rw [hid]
          ring
      _ < F.cheeger * F.cheeger * (η * F.scale (seq N) (bad N).i / 2) := by
          nlinarith
  -- The repair step.
  have hXcheeger : DirectedCoarea.HasCheegerLowerBound (modelX N)
      (Finset.univ.image (F.tags (seq N) (bad N).i)) F.cheeger := by
    rw [F.univ_image_tags]
    exact F.expands (seq N) (bad N).i
  have hZcheeger : DirectedCoarea.HasCheegerLowerBound (modelZ N)
      (Finset.univ.image (F.tags (seq N) (bad N).l)) F.cheeger := by
    rw [F.univ_image_tags]
    exact F.expands (seq N) (bad N).l
  have hrep := repairRelation_extractCrossing_candidate_and_close
    (F.tags (seq N) (bad N).i) (F.tags (seq N) (bad N).l) hXcheeger hZcheeger
    ((bad N).f.trans (bad N).g) U _ hE hsmallX hsmallZ hclose hforward
  -- The distance bound.
  have hham :
      (hammingDisagreement ((bad N).f.trans (bad N).g).swapPerm
        (repairRelation (sumModel (modelX N) (modelZ N)) U)).card ≤
      3 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card := by
    have h := card_repairRelation_disagreement_le (sumModel (modelX N) (modelZ N)) U
      ((bad N).f.trans (bad N).g).swapPerm
    rw [card_hammingDisagreement_comm]
    omega
  have hhamInv :
      (hammingDisagreement ((bad N).f.trans (bad N).g).swapPerm⁻¹
        (repairRelation (sumModel (modelX N) (modelZ N)) U)⁻¹).card ≤
      3 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
          ((bad N).f.trans (bad N).g).swapPerm).card := by
    rw [card_hammingDisagreement_inv]
    exact hham
  have hdist := twoSidedDisagreement_extractCrossing_le ((bad N).f.trans (bad N).g)
    (repairRelation (sumModel (modelX N) (modelZ N)) U)
  have hdistNat :
      ((bad N).f.trans (bad N).g).twoSidedDisagreement
          (extractCrossing (repairRelation (sumModel (modelX N) (modelZ N)) U)) ≤
        ((bad N).f.sourceDefect + (bad N).g.sourceDefect) +
          ((bad N).g.targetDefect + (bad N).f.targetDefect) +
          6 * (U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
            ((bad N).f.trans (bad N).g).swapPerm).card := by
    omega
  have hfsR := card_mul_sourceDefect_lt_of_candidate (bad N).hf
  have hftR := card_mul_targetDefect_lt_of_candidate (bad N).hf
  have hgsR := card_mul_sourceDefect_lt_of_candidate (bad N).hg
  have hgtR := card_mul_targetDefect_lt_of_candidate (bad N).hg
  have hdefReal :
      (((bad N).f.sourceDefect + (bad N).g.sourceDefect +
          ((bad N).g.targetDefect + (bad N).f.targetDefect) : ℕ) : ℝ) <
        3 * η * F.scale (seq N) (bad N).i := by
    push_cast
    have hfs0 : (0 : ℝ) ≤ (bad N).f.sourceDefect := by positivity
    have hft0 : (0 : ℝ) ≤ (bad N).f.targetDefect := by positivity
    have hgs0 : (0 : ℝ) ≤ (bad N).g.sourceDefect := by positivity
    have hgt0 : (0 : ℝ) ≤ (bad N).g.targetDefect := by positivity
    nlinarith
  have hcardXr : (F.scale (seq N) (bad N).i : ℝ) ≤
      (Fintype.card (F.model (seq N) (bad N).i) : ℝ) := by
    have h := hsz.1
    have h' : F.scale (seq N) (bad N).i ≤ Fintype.card (F.model (seq N) (bad N).i) := by
      omega
    exact_mod_cast h'
  have hdistReal :
      ((extractCrossing (repairRelation (sumModel (modelX N) (modelZ N)) U)).twoSidedDisagreement
          ((bad N).f.trans (bad N).g) : ℝ) ≤
        20000 * ζ * Fintype.card (F.model (seq N) (bad N).i) := by
    rw [twoSidedDisagreement_comm]
    have hcast :
        (((bad N).f.trans (bad N).g).twoSidedDisagreement
            (extractCrossing (repairRelation (sumModel (modelX N) (modelZ N)) U)) : ℝ) ≤
          (((bad N).f.sourceDefect + (bad N).g.sourceDefect +
            ((bad N).g.targetDefect + (bad N).f.targetDefect) : ℕ) : ℝ) +
          6 * ((U ∆ permutationGraph (sumModel (modelX N) (modelZ N))
            ((bad N).f.trans (bad N).g).swapPerm).card : ℝ) := by
      exact_mod_cast hdistNat
    have hζ0 : 0 ≤ ζ := by linarith
    nlinarith
  exact (bad N).noImprove
    (extractCrossing (repairRelation (sumModel (modelX N) (modelZ N)) U))
    ⟨hrep.1, by rw [twoSidedDisagreement_comm]; exact hrep.2, hdistReal⟩

/-! ### The joint choice of threshold and distance -/

theorem one_div_lt_of_nat_gt {a : ℝ} (ha : 0 < a) {j : ℕ} (hj : 1 / a < j) :
    1 / (100000 * ((j : ℝ) + 1)) < a := by
  have hpos : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hle : 1 / (100000 * ((j : ℝ) + 1)) ≤ 1 / ((j : ℝ) + 1) :=
    one_div_le_one_div_of_le hpos (by nlinarith)
  have hlt : 1 / ((j : ℝ) + 1) < a := by
    rw [div_lt_iff₀ hpos]
    have h := (div_lt_iff₀ ha).1 hj
    nlinarith
  linarith

open Classical in
/-- **Joint threshold and distance.**  The threshold `h n` and the distance
factor `d n` tend to zero, `h` dominates the prescribed vanishing sequence `ρ`,
and improvement with that threshold and distance holds eventually. -/
theorem exists_joint_improvement
    {Q : Finset K} {κ : ℝ} (hQ : IsKazhdanPair.{0, 0} K Q κ) (hQT : Q ⊆ T)
    (hone : (1 : K) ∈ T) (hκone : κ ≤ 1)
    (ρ : ℕ → ℝ) (hρ : Tendsto ρ atTop (𝓝 0)) :
    ∃ (h d : ℕ → ℝ), (∀ n, 0 < h n) ∧ Tendsto h atTop (𝓝 0) ∧
      Tendsto d atTop (𝓝 0) ∧ (∀ᶠ n in atTop, ρ n ≤ h n) ∧
      ∃ N₀ : ℕ, ∀ n ≥ N₀, F.ImproveCloseAt (h n) (d n) n := by
  classical
  obtain ⟨hq0, hq1⟩ := kazhdanFactor_nonneg_lt_one hQ T hone hκone
  have hs : 0 < T.card := Finset.card_pos.mpr ⟨1, hone⟩
  have hp := F.repairFactor_pos hone
  have hlevel : ∀ j : ℕ, ∃ (k : ℕ) (η δ : ℝ), 0 < k ∧ 0 < η ∧ 0 < δ ∧
      η < 1 / (100000 * ((j : ℝ) + 1)) ∧
      (k : ℝ) ^ 2 * η < 1 / (100000 * ((j : ℝ) + 1)) ∧
      16 * (T.card : ℝ) ^ 4 *
          (16 * (1 - κ ^ 2 / (4 * T.card)) ^ (2 * k) * (T.card : ℝ)⁻¹ * η + δ) <
        (((1 : ℝ) / 3) * (((2 : ℝ) / 3) - (1 : ℝ) / 3) ^ 2) ^ 2 *
          (F.repairFactor * η) ^ 4 := by
    intro j
    exact exists_repairParameters hq0 hq1 T.card hs hp (by positivity)
  choose kf ηf δf hk hη hδ hηζ hkη hnum using hlevel
  have hζ : ∀ j : ℕ, 1 / (100000 * ((j : ℝ) + 1)) ≤ 1 / 100000 := by
    intro j
    apply one_div_le_one_div_of_le (by norm_num)
    have hj : (0 : ℝ) ≤ j := by positivity
    nlinarith
  have hevent : ∀ j : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      F.ImproveCloseAt (ηf j) (20000 * (1 / (100000 * ((j : ℝ) + 1)))) n := by
    intro j
    exact F.eventually_improveCloseAt hQ hQT hone hκone (hk j) (hη j) (hδ j) (hζ j)
      (hηζ j) (hkη j) (hnum j)
  choose Nf hNf using hevent
  have hdom : ∀ j : ℕ, ∃ R : ℕ, ∀ n ≥ R, ρ n ≤ ηf j := by
    intro j
    have hev := (tendsto_order.1 hρ).2 (ηf j) (hη j)
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 hev
    exact ⟨R, fun n hn ↦ (hR n hn).le⟩
  choose Rf hRf using hdom
  let M : ℕ → ℕ := fun j ↦
    (Finset.range (j + 1)).sup fun i ↦ max (max (Nf i) (Rf i)) i
  have hMle : ∀ j, max (max (Nf j) (Rf j)) j ≤ M j := fun j ↦
    Finset.le_sup (f := fun i ↦ max (max (Nf i) (Rf i)) i)
      (Finset.mem_range.mpr (Nat.lt_succ_self j))
  have hNM : ∀ j, Nf j ≤ M j := fun j ↦
    ((le_max_left _ _).trans (le_max_left _ _)).trans (hMle j)
  have hRM : ∀ j, Rf j ≤ M j := fun j ↦
    ((le_max_right _ _).trans (le_max_left _ _)).trans (hMle j)
  have hjM : ∀ j, j ≤ M j := fun j ↦ (le_max_right _ _).trans (hMle j)
  let J : ℕ → ℕ := fun n ↦ Nat.findGreatest (fun j ↦ M j ≤ n) n
  have hJspec : ∀ n, M 0 ≤ n → M (J n) ≤ n := fun n hn ↦
    Nat.findGreatest_spec (P := fun j ↦ M j ≤ n) (Nat.zero_le n) hn
  have hJge : ∀ n j, M j ≤ n → j ≤ J n := fun n j hj ↦
    Nat.le_findGreatest (P := fun j ↦ M j ≤ n) ((hjM j).trans hj) hj
  refine ⟨fun n ↦ ηf (J n), fun n ↦ 20000 * (1 / (100000 * ((J n : ℝ) + 1))),
    fun n ↦ hη (J n), ?_, ?_, ?_, M 0, ?_⟩
  · refine tendsto_order.2 ⟨fun a ha ↦ Filter.Eventually.of_forall fun n ↦
      lt_of_lt_of_le ha (hη (J n)).le, fun a ha ↦ ?_⟩
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / a)
    rw [Filter.eventually_atTop]
    refine ⟨M j, fun n hn ↦ ?_⟩
    have hJ := hJge n j hn
    have hlt := one_div_lt_of_nat_gt ha hj
    have hmono : 1 / (100000 * ((J n : ℝ) + 1)) ≤ 1 / (100000 * ((j : ℝ) + 1)) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (j : ℝ) ≤ J n := by exact_mod_cast hJ
      nlinarith
    exact ((hηζ (J n)).trans_le hmono).trans hlt
  · refine tendsto_order.2 ⟨fun a ha ↦ Filter.Eventually.of_forall fun n ↦ ?_,
      fun a ha ↦ ?_⟩
    · have : (0 : ℝ) < 20000 * (1 / (100000 * ((J n : ℝ) + 1))) := by positivity
      linarith
    · obtain ⟨j, hj⟩ := exists_nat_gt (1 / (a / 20000))
      rw [Filter.eventually_atTop]
      refine ⟨M j, fun n hn ↦ ?_⟩
      have hJ := hJge n j hn
      have ha' : 0 < a / 20000 := by positivity
      have hlt := one_div_lt_of_nat_gt ha' hj
      have hmono : 1 / (100000 * ((J n : ℝ) + 1)) ≤ 1 / (100000 * ((j : ℝ) + 1)) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (j : ℝ) ≤ J n := by exact_mod_cast hJ
        nlinarith
      have h := hmono.trans_lt hlt
      have h20 := mul_lt_mul_of_pos_left h (by norm_num : (0 : ℝ) < 20000)
      have hdiv : (20000 : ℝ) * (a / 20000) = a := by ring
      linarith
  · rw [Filter.eventually_atTop]
    exact ⟨M 0, fun n hn ↦ hRf (J n) n ((hRM (J n)).trans (hJspec n hn))⟩
  · intro n hn
    exact hNf (J n) n ((hNM (J n)).trans (hJspec n hn))

end ComponentFamily

end CentralizerNormalizationImprove
end GroupApproximation
