import GroupApproximation.GGT.HullSCLemma44RelativeBoundary

/-!
# Linear relative area from Hull's Lemma 4.4 cut

Osin's proof of Theorem 4.1 uses Lemma 4.4 to remove one relator cell while
strictly shortening the boundary word.  Strong induction on boundary length
then bounds the number of removed cells by the original length.  This is the
linear relative-area assertion in Osin Lemma 5.1, equations (18)--(21).

`HullSCLemma44RelativeDehn` identifies the exact conjugate removed by one cut.
This file performs the induction and packages its result as
`RelativeLinearKernelArea`.  The conclusion refers to the existing
`RelatorDefectBudget.IsRelatorProduct` predicate, so it is independent of the
combinatorial-map representation used to obtain the cut.

The final theorem applies the prescribed-boundary construction and a
Greendlinger certificate for every reduced diagram.  The remaining passage
from this linear relative Dehn function to a hyperbolic quotient relative
Cayley graph is Osin Theorem 1.7; local finiteness of the transported relative
metrics additionally uses the finite component-letter support.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

/-! ## Relator-product facts -/

/-- A bounded product of conjugates of `R` lies in its normal closure. -/
theorem isRelatorProduct_mem_normalClosure
    {G : Type u} [Group G] {R : Set G} {area : ℕ} {g : G}
    (h : RelatorDefectBudget.IsRelatorProduct R area g) :
    g ∈ Subgroup.normalClosure R := by
  induction h with
  | one => exact Subgroup.one_mem _
  | base hr => exact Subgroup.subset_normalClosure hr
  | inv h ih => exact Subgroup.inv_mem _ ih
  | conj c h ih =>
      exact Subgroup.normalClosure_normal.conj_mem _ ih c
  | mul ha hb iha ihb => exact Subgroup.mul_mem _ iha ihb

/-- If a homomorphism kills every element of `R`, it kills every bounded
relator product over `R`. -/
theorem map_eq_one_of_isRelatorProduct
    {G : Type u} {Q : Type v} [Group G] [Group Q]
    {R : Set G} (q : G →* Q) (hkill : ∀ r ∈ R, q r = 1)
    {area : ℕ} {g : G}
    (h : RelatorDefectBudget.IsRelatorProduct R area g) : q g = 1 := by
  induction h with
  | one => exact map_one q
  | base hr => exact hkill _ hr
  | inv h ih => rw [map_inv, ih, inv_one]
  | conj c h ih => rw [map_mul, map_mul, map_inv, ih]; group
  | mul ha hb iha ihb => rw [map_mul, iha, ihb, mul_one]

/-! ## The linear-area predicate -/

/-- Every quotient-null word on the source relative alphabet is a product of
at most its length many conjugates of selected relator values.  This is the
linear relative Dehn function produced in Osin Lemma 5.1. -/
def RelativeLinearKernelArea
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (q : G →* Q) : Prop :=
  ∀ boundaryWord : List G,
    IsWord D.alphabet.carrier boundaryWord boundaryWord.prod →
      q boundaryWord.prod = 1 →
        ∃ area : ℕ, area ≤ boundaryWord.length ∧
          RelatorDefectBudget.IsRelatorProduct
            (GGT.RelLetter.listVal '' W) area boundaryWord.prod

namespace RelativeLinearKernelArea

/-- A linear-area witness places every quotient-null source word in the
relator normal closure. -/
theorem word_prod_mem_normalClosure
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    (H : RelativeLinearKernelArea D W q) (boundaryWord : List G)
    (hword : IsWord D.alphabet.carrier boundaryWord boundaryWord.prod)
    (hmap : q boundaryWord.prod = 1) :
    boundaryWord.prod ∈
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
  obtain ⟨area, _, harea⟩ := H boundaryWord hword hmap
  exact isRelatorProduct_mem_normalClosure harea

/-- Together with relator killing, linear area recovers the expected kernel
equation. -/
theorem ker_eq_normalClosure
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))} {q : G →* Q}
    (H : RelativeLinearKernelArea D W q)
    (hkill : ∀ relator ∈ W,
      q (GGT.RelLetter.listVal relator) = 1) :
    q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨boundaryWord, hword⟩ :=
      exists_isWord D.alphabet.symmetricGenerating g
    have hwordProd : IsWord D.alphabet.carrier boundaryWord boundaryWord.prod :=
      ⟨hword.letters, rfl⟩
    rw [← hword.prod_eq]
    apply H.word_prod_mem_normalClosure boundaryWord hwordProd
    rw [hword.prod_eq]
    exact MonoidHom.mem_ker.mp hg
  · apply Subgroup.normalClosure_le_normal
    intro value hvalue
    obtain ⟨relator, hrelator, rfl⟩ := hvalue
    exact MonoidHom.mem_ker.mpr (hkill relator hrelator)

end RelativeLinearKernelArea

/-! ## Boundary-length induction -/

/-- A strict one-relator cut for every nonidentity quotient-null boundary
word gives a linear relative-area bound. -/
theorem relativeLinearKernelArea_of_dehnCuts
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda))) (eps : ℕ)
    (q : G →* Q)
    (hcuts : ∀ boundaryWord : List G,
      IsWord D.alphabet.carrier boundaryWord boundaryWord.prod →
      boundaryWord.prod ≠ 1 → q boundaryWord.prod = 1 →
        Nonempty (RelativeDehnCut D W eps q boundaryWord)) :
    RelativeLinearKernelArea D W q := by
  intro boundaryWord hword hmap
  let P : ℕ → Prop := fun length =>
    ∀ word : List G, word.length = length →
      IsWord D.alphabet.carrier word word.prod → q word.prod = 1 →
        ∃ area : ℕ, area ≤ word.length ∧
          RelatorDefectBudget.IsRelatorProduct
            (GGT.RelLetter.listVal '' W) area word.prod
  have hlinear : ∀ length : ℕ, P length := by
    intro length
    induction length using Nat.strong_induction_on with
    | _ length ih =>
      intro word hlength hword' hmap'
      by_cases hone : word.prod = 1
      · refine ⟨0, Nat.zero_le _, ?_⟩
        rw [hone]
        exact RelatorDefectBudget.IsRelatorProduct.one
      · obtain ⟨C⟩ := hcuts word hword' hone hmap'
        have hshortLength :
            C.contiguity.shortenedBoundaryWord.length < length := by
          rw [← hlength]
          exact C.length_lt
        have hshortMap :
            q C.contiguity.shortenedBoundaryWord.prod = 1 :=
          C.quotient_value.trans hmap'
        obtain ⟨area, hareaLength, harea⟩ :=
          ih C.contiguity.shortenedBoundaryWord.length hshortLength
            C.contiguity.shortenedBoundaryWord rfl C.shortenedWord_isWord
              hshortMap
        let conjugator : G := C.contiguity.boundaryBefore.prod *
          (GGT.RelLetter.listVal C.contiguity.leftSide)⁻¹
        have hbase : RelatorDefectBudget.IsRelatorProduct
            (GGT.RelLetter.listVal '' W) 1
              (GGT.RelLetter.listVal C.relator) :=
          RelatorDefectBudget.IsRelatorProduct.base
            ⟨C.relator, C.relator_mem, rfl⟩
        have hstep : RelatorDefectBudget.IsRelatorProduct
            (GGT.RelLetter.listVal '' W) (1 + area)
              (conjugator * GGT.RelLetter.listVal C.relator *
                conjugator⁻¹ *
                  C.contiguity.shortenedBoundaryWord.prod) :=
          (hbase.conj conjugator).mul harea
        refine ⟨1 + area, ?_, ?_⟩
        · omega
        · rw [C.contiguity.boundaryWord_prod_eq_conjugate_relator_mul_shortened]
          exact hstep
  exact hlinear boundaryWord.length boundaryWord rfl hword hmap

/-- Certificates for every prescribed reduced boundary give Osin Lemma 5.1's
linear relative-area conclusion. -/
theorem relativeLinearKernelArea_of_certificates
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000) (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
      Nonempty (RelativeDiagramCertificate D W eps mu Z)) :
    RelativeLinearKernelArea D W q := by
  apply relativeLinearKernelArea_of_dehnCuts D W eps q
  intro boundaryWord hword hne hmap
  exact exists_relativeDehnCut_of_kernelWord D hsc hmu hrho q hker hcert
    boundaryWord hword hne hmap

/-! ## Model tests -/

/-- An injective map has the empty-family linear-area property: every
quotient-null boundary already represents the identity and uses zero cells. -/
theorem relativeLinearKernelArea_empty_of_injective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Injective q) :
    RelativeLinearKernelArea D
      (∅ : Set (List (GGT.RelLetter G Lambda))) q := by
  intro boundaryWord hword hmap
  have hone : boundaryWord.prod = 1 := by
    apply hq
    rw [hmap, map_one]
  refine ⟨0, Nat.zero_le _, ?_⟩
  rw [hone]
  exact RelatorDefectBudget.IsRelatorProduct.one

/-- The one-point source supplies the smallest concrete model of linear
relative area, independently of the chosen relator family. -/
theorem relativeLinearKernelArea_trivialSource
    {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet PUnit Lambda) (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (q : PUnit →* Q) : RelativeLinearKernelArea D W q := by
  intro boundaryWord hword hmap
  have hone : boundaryWord.prod = 1 := Subsingleton.elim _ _
  refine ⟨0, Nat.zero_le _, ?_⟩
  rw [hone]
  exact RelatorDefectBudget.IsRelatorProduct.one

end HullSC
end GroupApproximation
