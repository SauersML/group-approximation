import GroupApproximation.GGT.RelHypOsin24Construction
import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullYiFiniteFamilyPair
import GroupApproximation.GGT.HullYiFiniteFamilyInduction

/-!
# Glue between Hull's quotient conclusions and Osin's Theorem 2.4

Hull's Lemma 4.9 gives a quotient-free correction statement for powers in the
normal closure of one relator.  The first section turns that statement into
Osin's finite-order lifting clause, both for a fixed quotient and directly
from `HullLemma49KernelPowerStatement`.

The second section checks the proposed DGO Proposition 4.28 bridge against the
two relative-metric definitions currently in the repository.  They are not
equivalent.  `RelHyp.RelativeGeneratingSet.AvoidsPeripheral` forgets the label
of an edge and excludes every step whose endpoints lie in the selected
peripheral.  `GGT.AvoidsFrom` retains labels and excludes only a component
letter carrying that peripheral's index.  Two equal infinite peripherals give
a smallest counterexample: the first metric has only the identity at finite
distance, while the second has the whole group in its radius-one ball by using
the other component label.

Thus the finite-order part of the Hull-to-Osin route composes now.  The
relative-hyperbolicity part cannot be obtained by identifying the two current
definitions; its repair must make Osin's relative paths label-sensitive, or
state relative hyperbolicity directly through `GGT.RelGenSet`.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The shared Yi input gives the pair form -/

/-- The finite-avoidance Yi statement requested by the Hull construction
contains the two-element Yi statement used by the existing Fournier--Facio
reduction.  The first implication is the proved finite-family induction; the
second is specialization of Hull's printed all-finite-family assertion at two
elements. -/
theorem yiSuitablePair_of_avoidingFiniteOneSided
    (hyi : HullSC.YiSuitablePairAvoidingFiniteOneSided.{u}) :
    HullSC.YiSuitablePair.{u} :=
  HullSC.yiSuitablePair_of_finiteFamily
    (HullSC.yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided.mpr hyi)

/-! ## Hull Lemma 4.9 gives Osin's finite-order lift -/

/-- Hull's quotient-free kernel-power correction gives exactly the
finite-order lifting clause of Osin's Theorem 2.4.  The order-preserving lift
proved by `kernelPowerCorrection_iff_finiteOrderLift` is stronger than the
conclusion used here. -/
theorem isOsin24TorsionConclusion_of_kernelPowerCorrection
    {G : Type u} [Group G] {Q : Type w} [Group Q] (eta : G →* Q)
    (hsurj : Function.Surjective eta)
    (hcorrect : HullSC.KernelPowerCorrection eta.ker) :
    IsOsin24TorsionConclusion eta := by
  intro q hq
  have hlift :=
    (HullSC.kernelPowerCorrection_iff_finiteOrderLift eta hsurj).mp hcorrect
  obtain ⟨g, hmap, horder⟩ := hlift q hq
  have hg : IsOfFinOrder g := by
    rw [← orderOf_pos_iff, horder]
    exact hq.orderOf_pos
  exact ⟨g, hg, hmap⟩

/-- Hull's Lemma 4.9, applied to the one-relator quotient, supplies Osin's
finite-order lifting conclusion.  The constants retain Hull's source order:
the relative structure and its acylindrical action are fixed before the
small-cancellation parameters and relator family are chosen. -/
theorem exists_isOsin24TorsionConclusion_of_lemma49
    (h49 : HullSC.HullLemma49KernelPowerStatement.{u, w})
    {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (hemb : D.IsHyperbolicallyEmbedded)
    (hacy : IsAcylindrical G (Cayley D.alphabet)) :
    ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
      ∀ (W : Set (List (RelLetter G Lambda)))
        (v : List (RelLetter G Lambda)), v ∈ W →
          HullSC.RelWord.IsLemma49Input D W eps mu rho →
            ∀ {Q : Type w} [Group Q] (eta : G →* Q),
              Function.Surjective eta →
                eta.ker = Subgroup.normalClosure
                  ({RelLetter.listVal v} : Set G) →
                    IsOsin24TorsionConclusion eta := by
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := h49 D hemb hacy
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hinput Q _ eta hsurj hker
  have hnormal : HullSC.KernelPowerCorrection
      (Subgroup.normalClosure ({RelLetter.listVal v} : Set G)) :=
    hgood W v hv hinput
  have hcorrect : HullSC.KernelPowerCorrection eta.ker := by
    rw [hker]
    exact hnormal
  exact isOsin24TorsionConclusion_of_kernelPowerCorrection eta hsurj hcorrect

/-! ## The two current relative metrics disagree -/

namespace RelativeMetricCountermodel

/-- An infinite group used to separate the endpoint and labelled relative
metrics. -/
abbrev DuplicateGroup : Type := Multiplicative ℤ

/-- The peripheral family with two different indices naming the whole group. -/
abbrev duplicateFamily : Bool → Subgroup DuplicateGroup := fun _ ⇒ ⊤

/-- The empty finite relative base generates relative to the duplicate top
family. -/
def duplicateRelativeGeneratingSet :
    RelativeGeneratingSet DuplicateGroup duplicateFamily where
  carrier := ∅
  finite := Set.finite_empty
  inv_mem := by simp
  closure_eq := by
    rw [eq_top_iff]
    intro x _hx
    apply Subgroup.subset_closure
    exact Or.inr (Set.mem_iUnion.mpr ⟨false, Subgroup.mem_top x⟩)

/-- When the selected peripheral is the whole group, an endpoint-avoiding path
must be empty. -/
theorem avoidsPeripheral_duplicate_eq_nil (l : Bool)
    {v : List DuplicateGroup}
    (h : RelativeGeneratingSet.AvoidsPeripheral duplicateFamily l v) :
    v = [] := by
  cases v with
  | nil => rfl
  | cons a v =>
      exfalso
      exact h 0 (by simp) ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩

/-- Consequently every finite ball for the endpoint-only peripheral metric is
contained in the singleton identity set. -/
theorem duplicate_peripheralMetricBall_subset_singleton (l : Bool) (n : ℕ) :
    {h : DuplicateGroup |
      h ∈ duplicateFamily l ∧
        ∃ m ∈ duplicateRelativeGeneratingSet.peripheralLengths l h,
          m ≤ n} ⊆ ({1} : Set DuplicateGroup) := by
  intro h hh
  obtain ⟨_hmem, m, w, hword, hav, _hlen, _hmn⟩ := hh
  have hw : w = [] := avoidsPeripheral_duplicate_eq_nil l hav
  subst w
  simpa using hword.prod_eq.symm

/-- The endpoint-only metric therefore declares the duplicate family locally
finite. -/
theorem duplicate_peripheralMetricLocallyFinite :
    PeripheralMetricLocallyFinite duplicateRelativeGeneratingSet := by
  intro l n
  exact Set.Finite.subset (Set.finite_singleton 1)
    (duplicate_peripheralMetricBall_subset_singleton l n)

/-- Every element is a letter of the relative alphabet because either copy of
the top subgroup supplies it. -/
theorem mem_duplicateRelativeAlphabet (x : DuplicateGroup) :
    x ∈ duplicateRelativeGeneratingSet.alphabet.carrier := by
  exact Or.inr (Set.mem_iUnion.mpr ⟨false, Subgroup.mem_top x⟩)

/-- The duplicate relative Cayley graph has diameter at most one. -/
theorem duplicateRelative_dist_le_one
    (x y : Cayley duplicateRelativeGeneratingSet.alphabet) :
    dist x y ≤ (1 : ℝ) := by
  have hnorm : wordNorm duplicateRelativeGeneratingSet.alphabet.carrier
      ((Cayley.val x)⁻¹ * Cayley.val y) ≤ 1 :=
    wordNorm_le_one_of_mem
      (mem_duplicateRelativeAlphabet ((Cayley.val x)⁻¹ * Cayley.val y))
  have hdist : wordDist duplicateRelativeGeneratingSet.alphabet.carrier
      (Cayley.val x) (Cayley.val y) ≤ 1 := hnorm
  rw [Cayley.dist_eq]
  exact_mod_cast hdist

/-- In the repository's current endpoint-only definition, an infinite group
is relatively hyperbolic with respect to two identical copies of itself. -/
theorem duplicate_isRelativelyHyperbolic :
    IsRelativelyHyperbolic DuplicateGroup duplicateFamily := by
  refine ⟨duplicateRelativeGeneratingSet, 1, ?_,
    duplicate_peripheralMetricLocallyFinite⟩
  exact isHyperbolicSpace_of_bounded duplicateRelative_dist_le_one

/-- The labelled `RelGenSet` reading of the same base and family. -/
def duplicateRelGenSet : RelGenSet DuplicateGroup Bool where
  base := ∅
  fam := duplicateFamily
  symmetricGenerating := by
    refine ⟨?_, ?_⟩
    · intro x _hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨false, Subgroup.mem_top x⁻¹⟩)
    · rw [eq_top_iff]
      intro x _hx
      apply Subgroup.subset_closure
      exact Or.inr (Set.mem_iUnion.mpr ⟨false, Subgroup.mem_top x⟩)

/-- Every group element lies in the labelled radius-one ball at `false`: use
the `true` component label, which is not an edge of the `false` peripheral
subgraph even though it has the same group value. -/
theorem univ_subset_duplicateRelBall :
    (Set.univ : Set DuplicateGroup) ⊆ duplicateRelGenSet.relBall false 1 := by
  intro x _hx
  rw [RelGenSet.mem_relBall]
  refine ⟨Subgroup.mem_top x, [RelLetter.comp true x], ?_, ?_, ?_, by simp⟩
  · intro a ha
    have ha' : a = RelLetter.comp true x := by simpa using ha
    subst a
    exact Subgroup.mem_top x
  · simp [RelLetter.listVal, RelLetter.val]
  · simp [AvoidsFrom, RelLetter.IsCompOf]

/-- The same family is not hyperbolically embedded in the labelled DGO
metric, because its radius-one ball is infinite. -/
theorem duplicateRelGenSet_not_isHyperbolicallyEmbedded :
    ¬ duplicateRelGenSet.IsHyperbolicallyEmbedded := by
  intro hemb
  have hfinite : (Set.univ : Set DuplicateGroup).Finite :=
    Set.Finite.subset (hemb.locallyFinite false 1)
      univ_subset_duplicateRelBall
  exact Set.infinite_univ hfinite

end RelativeMetricCountermodel

end RelHyp
end GGT
end GroupApproximation
