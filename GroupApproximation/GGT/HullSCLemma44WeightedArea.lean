import GroupApproximation.GGT.HullSCLemma44PrefixCutRatio
import GroupApproximation.GGT.HullSCLemma44RelativeBoundary

/-!
# Weighted relative area from quantitative Greendlinger cuts

The ordinary area induction counts one unit for each selected relator cell.
The prefix presentation also has to expand that cell into consecutive-prefix
triangles, so its cost is the length of the cell label.  This file performs
the weighted induction needed for that expansion.

At one cut, the label length is at most five times the removed boundary arc,
and the replacement has at most half the arc length.  Charging ten units to
each current boundary letter pays both the recursive boundary and the new
cell label.  The result is a total relator-length budget at most ten times the
initial boundary length.  This is the weighted form of equations (18)--(21)
in Osin's proof of Lemma 5.1.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

/-! ## Products weighted by relator length -/

namespace RelatorLengthBudget

/-- A product of conjugates of values of words in `W`, indexed by the sum of
the lengths of the selected words. -/
inductive IsWeightedRelatorProduct
    {G : Type u} [Group G] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) : ℕ → G → Prop
  | one : IsWeightedRelatorProduct W 0 1
  | base {word : List (GGT.RelLetter G Lambda)} (hword : word ∈ W) :
      IsWeightedRelatorProduct W word.length (GGT.RelLetter.listVal word)
  | inv {weight : ℕ} {g : G} :
      IsWeightedRelatorProduct W weight g →
        IsWeightedRelatorProduct W weight g⁻¹
  | conj {weight : ℕ} {g : G} :
      IsWeightedRelatorProduct W weight g → ∀ c : G,
        IsWeightedRelatorProduct W weight (c * g * c⁻¹)
  | mul {leftWeight rightWeight : ℕ} {g h : G} :
      IsWeightedRelatorProduct W leftWeight g →
      IsWeightedRelatorProduct W rightWeight h →
        IsWeightedRelatorProduct W (leftWeight + rightWeight) (g * h)

namespace IsWeightedRelatorProduct

/-- Weighted relator products lie in the normal closure of the relator
values. -/
theorem mem_normalClosure
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {weight : ℕ} {g : G}
    (h : IsWeightedRelatorProduct W weight g) :
    g ∈ Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
  induction h with
  | one => exact Subgroup.one_mem _
  | base hword =>
      exact Subgroup.subset_normalClosure ⟨_, hword, rfl⟩
  | inv h ih => exact Subgroup.inv_mem _ ih
  | conj h c ih => exact Subgroup.normalClosure_normal.conj_mem _ ih c
  | mul hleft hright ihleft ihright =>
      exact Subgroup.mul_mem _ ihleft ihright

/-- A relator family with no empty word converts weighted products to
ordinary products whose cell count is at most the weight. -/
theorem exists_isRelatorProduct_le
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    (hpositive : ∀ word ∈ W, 0 < word.length)
    {weight : ℕ} {g : G}
    (h : IsWeightedRelatorProduct W weight g) :
    ∃ area : ℕ, area ≤ weight ∧
      RelatorDefectBudget.IsRelatorProduct
        (GGT.RelLetter.listVal '' W) area g := by
  induction h with
  | one => exact ⟨0, le_rfl, RelatorDefectBudget.IsRelatorProduct.one⟩
  | @base word hword =>
      refine ⟨1, hpositive word hword, ?_⟩
      exact RelatorDefectBudget.IsRelatorProduct.base ⟨word, hword, rfl⟩
  | inv h ih =>
      obtain ⟨area, harea, hproduct⟩ := ih
      exact ⟨area, harea, hproduct.inv⟩
  | conj h c ih =>
      obtain ⟨area, harea, hproduct⟩ := ih
      exact ⟨area, harea, hproduct.conj c⟩
  | mul hleft hright ihleft ihright =>
      obtain ⟨leftArea, hleftArea, hleftProduct⟩ := ihleft
      obtain ⟨rightArea, hrightArea, hrightProduct⟩ := ihright
      exact ⟨leftArea + rightArea, Nat.add_le_add hleftArea hrightArea,
        hleftProduct.mul hrightProduct⟩

end IsWeightedRelatorProduct
end RelatorLengthBudget

/-! ## Ratio-controlled cuts -/

/-- A Dehn cut with the two quantitative estimates used by the weighted
potential argument. -/
structure RatioRelativeDehnCut
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (eps : ℕ)
    (q : G →* Q) (boundaryWord : List G) where
  cut : RelativeDehnCut D W eps q boundaryWord
  replacement_twice_le :
    2 * cut.contiguity.replacementWord.length ≤
      cut.contiguity.boundaryArc.length
  relator_length_le :
    cut.relator.length ≤ 5 * cut.contiguity.boundaryArc.length

namespace RatioRelativeDehnCut

/-- A ratio-controlled cut is in particular a strict Dehn cut. -/
theorem length_lt
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {eps : ℕ}
    {q : G →* Q} {boundaryWord : List G}
    (C : RatioRelativeDehnCut D W eps q boundaryWord) :
    C.cut.contiguity.shortenedBoundaryWord.length < boundaryWord.length :=
  C.cut.length_lt

end RatioRelativeDehnCut

/-! ## The weighted kernel-area predicate -/

/-- Every quotient-null source word has a relator product whose total label
length is at most ten times the boundary length. -/
def RelativeWeightedKernelArea
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (q : G →* Q) : Prop :=
  ∀ boundaryWord : List G,
    IsWord D.alphabet.carrier boundaryWord boundaryWord.prod →
      q boundaryWord.prod = 1 →
        ∃ weight : ℕ, weight ≤ 10 * boundaryWord.length ∧
          RelatorLengthBudget.IsWeightedRelatorProduct W weight
            boundaryWord.prod

/-! ## Boundary-length induction -/

/-- Ratio-controlled cuts for all nonidentity quotient-null words give the
linear weighted area bound. -/
theorem relativeWeightedKernelArea_of_ratioCuts
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (eps : ℕ)
    (q : G →* Q)
    (hcuts : ∀ boundaryWord : List G,
      IsWord D.alphabet.carrier boundaryWord boundaryWord.prod →
      boundaryWord.prod ≠ 1 → q boundaryWord.prod = 1 →
        Nonempty (RatioRelativeDehnCut D W eps q boundaryWord)) :
    RelativeWeightedKernelArea D W q := by
  intro boundaryWord hword hmap
  let P : ℕ → Prop := fun length =>
    ∀ word : List G, word.length = length →
      IsWord D.alphabet.carrier word word.prod → q word.prod = 1 →
        ∃ weight : ℕ, weight ≤ 10 * word.length ∧
          RelatorLengthBudget.IsWeightedRelatorProduct W weight word.prod
  have hlinear : ∀ length : ℕ, P length := by
    intro length
    induction length using Nat.strong_induction_on with
    | _ length ih =>
      intro word hlength hword' hmap'
      by_cases hone : word.prod = 1
      · refine ⟨0, Nat.zero_le _, ?_⟩
        rw [hone]
        exact RelatorLengthBudget.IsWeightedRelatorProduct.one
      · obtain ⟨C⟩ := hcuts word hword' hone hmap'
        have hshortLength :
            C.cut.contiguity.shortenedBoundaryWord.length < length := by
          rw [← hlength]
          exact C.length_lt
        have hshortMap :
            q C.cut.contiguity.shortenedBoundaryWord.prod = 1 :=
          C.cut.quotient_value.trans hmap'
        obtain ⟨weight, hweightLength, hweight⟩ :=
          ih C.cut.contiguity.shortenedBoundaryWord.length hshortLength
            C.cut.contiguity.shortenedBoundaryWord rfl
              C.cut.shortenedWord_isWord hshortMap
        let conjugator : G := C.cut.contiguity.boundaryBefore.prod *
          (GGT.RelLetter.listVal C.cut.contiguity.leftSide)⁻¹
        have hbase : RelatorLengthBudget.IsWeightedRelatorProduct W
            C.cut.relator.length (GGT.RelLetter.listVal C.cut.relator) :=
          RelatorLengthBudget.IsWeightedRelatorProduct.base C.cut.relator_mem
        have hstep : RelatorLengthBudget.IsWeightedRelatorProduct W
            (C.cut.relator.length + weight)
            (conjugator * GGT.RelLetter.listVal C.cut.relator *
              conjugator⁻¹ * C.cut.contiguity.shortenedBoundaryWord.prod) :=
          (hbase.conj conjugator).mul hweight
        have hboundaryLength :=
          congrArg List.length C.cut.contiguity.boundary_decomposition
        have hshortenedLength := C.cut.contiguity.shortenedBoundaryWord_length
        have hratio : 2 * C.cut.contiguity.replacementWord.length ≤
            C.cut.contiguity.boundaryArc.length := C.replacement_twice_le
        have hrelator : C.cut.relator.length ≤
            5 * C.cut.contiguity.boundaryArc.length := C.relator_length_le
        simp only [List.length_append] at hboundaryLength
        refine ⟨C.cut.relator.length + weight, ?_, ?_⟩
        · omega
        · rw [C.cut.contiguity.boundaryWord_prod_eq_conjugate_relator_mul_shortened]
          exact hstep
  exact hlinear boundaryWord.length boundaryWord rfl hword hmap

/-! ## Certificate construction -/

/-- A certificate at the stronger threshold supplies a ratio-controlled cut
for its designated boundary. -/
theorem exists_ratioRelativeDehnCut_of_certificate
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {R eps rho : ℕ} {mu : ℝ}
    {Z : RelativeReducedDiagram D W R}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 100 * (eps + 1) ≤ rho)
    (K : RelativeDiagramCertificate D W eps mu Z)
    (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    Nonempty (RatioRelativeDehnCut D W eps q K.boundaryWord) := by
  obtain ⟨i, C, _, hratio, hrelator, harcPos⟩ :=
    RelativeBoundaryContiguity.exists_ratio_bounded_cut_of_certificate
      D hsc hmu hrho K
  have hboundary : IsWord D.alphabet.carrier K.boundaryWord
      K.boundaryWord.prod := by
    refine ⟨?_, rfl⟩
    intro x hx
    apply Z.boundaryWord_isWord.letters x
    rwa [← K.boundaryWord_eq]
  have hrelatorAdmissible : RelWord.IsAdmissible D (K.cellLabel i) :=
    hsc.admissible (K.cellLabel i) (K.cellLabel_mem i)
  have hkill : q (GGT.RelLetter.listVal (K.cellLabel i)) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [hker]
    exact Subgroup.subset_normalClosure
      ⟨K.cellLabel i, K.cellLabel_mem i, rfl⟩
  have hshort : C.replacementWord.length < C.boundaryArc.length :=
    C.replacementWord_length_lt_boundaryArc_of_twice_le harcPos hratio
  refine ⟨{
    cut := {
      relator := K.cellLabel i
      relator_mem := K.cellLabel_mem i
      contiguity := C
      shortenedWord_isWord := C.shortenedBoundaryWord_isWord hboundary
        hrelatorAdmissible
      quotient_value := C.map_shortenedBoundaryWord_prod_eq q hkill
      replacement_length_lt := hshort }
    replacement_twice_le := hratio
    relator_length_le := hrelator }⟩

/-- Certificates for all prescribed reduced boundaries give the weighted
linear area estimate. -/
theorem relativeWeightedKernelArea_of_certificates
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 100 * (eps + 1) ≤ rho)
    (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    RelativeWeightedKernelArea D W q := by
  apply relativeWeightedKernelArea_of_ratioCuts D W eps q
  intro boundaryWord hword hne hmap
  have hnormal : boundaryWord.prod ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) :=
    mem_normalClosure_of_map_eq_one q hker hmap
  obtain ⟨Z, hZboundary⟩ := exists_relativeReducedDiagram_of_boundaryWord
    D W hsc.toIsSmallCancellation boundaryWord boundaryWord.prod hword hne hnormal
  obtain ⟨K⟩ := hcert boundaryWord.length Z
  have hcut := exists_ratioRelativeDehnCut_of_certificate
    D hsc hmu hrho K q hker
  rw [K.boundaryWord_eq, hZboundary] at hcut
  exact hcut

end HullSC
end GroupApproximation
