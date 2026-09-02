import GroupApproximation.GGT.HullSCLemma44KernelGeodesicCut
import GroupApproximation.GGT.HullSCLemma44KernelGeodesicInduction

/-!
# Constructing the kernel-geodesic induction step

The least-area argument has two separable inputs.  A relative diagram and its
Greendlinger certificate produce the shorter kernel word by
`exists_shorter_kernelGeodesic_of_relativeDiagramCertificate`.  The planar
prefix-arc calculation supplies the transfer of bounds from the shorter word
to the old word.  `KernelGeodesicCutData` names those inputs at one explicit
area, and the theorems below construct `KernelGeodesicCutStep` and perform the
strong induction on that area.

The natural-number measure is the designated geodesic boundary length.  The
strict inequality is inherited from the exterior-arc replacement, so the
induction has no hidden termination premise.  The only remaining vk datum is
the displayed `prefix_transfer` field, whose statement is the exact boundary
prefix lemma still needed by the planar producer.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

/-- A least-area certificate together with the one planar prefix calculation
needed after cutting its selected exterior arc.  The diagram boundary is the
current geodesic word, so its area and boundary length are explicit. -/
structure KernelGeodesicCutData
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (M area : ℕ) (word : List G) where
  diagram : RelativeReducedDiagram D W word.length
  diagram_boundary : diagram.boundaryWord = word
  certificate : RelativeDiagramCertificate D W eps mu diagram
  /-- Every prefix bound for the shorter geodesic transfers across the
  selected boundary arc.  This is the exact vk boundary-prefix estimate. -/
  prefix_transfer :
    ∀ (nextKernel : G) (nextWord : List G),
      nextKernel ∈ q.ker →
      nextWord.prod = nextKernel →
      (∀ x ∈ nextWord,
        x ∈ (D.adjoinRelatorPrefixes W
          hsc.toIsSmallCancellation).alphabet.carrier) →
      nextWord.length < word.length →
      nextWord.length = wordDist
        (D.adjoinRelatorPrefixes W
          hsc.toIsSmallCancellation).alphabet.carrier 1 nextKernel →
      (∀ i ≤ nextWord.length,
        wordDist
          ((D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).adjoinKernel q).alphabet.carrier
          1 (nextWord.take i).prod ≤ M) →
      ∀ i ≤ word.length,
        wordDist
          ((D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).adjoinKernel q).alphabet.carrier
          1 (word.take i).prod ≤ M

/-- The certificate data performs one actual cut and constructs every field of
`KernelGeodesicCutStep`, including the new kernel endpoint and its area. -/
theorem kernelGeodesicCutStep_of_data
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (M area : ℕ) (endpoint : G) (word : List G)
    (hendpoint : endpoint ∈ q.ker)
    (_hword : ∀ x ∈ word,
      x ∈ (D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).alphabet.carrier)
    (hprod : word.prod = endpoint)
    (hgeodesic : word.length = wordDist
      (D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).alphabet.carrier 1 endpoint)
    (harea : word.length = area)
    (_hne : word.prod ≠ 1)
    (data : KernelGeodesicCutData D W eps rho mu hsc q M area word)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W)) :
    Nonempty (KernelGeodesicCutStep D W eps rho mu hsc q M area word) := by
  have hboundary : q data.certificate.boundaryWord.prod = 1 := by
    rw [data.certificate.boundaryWord_eq, data.diagram_boundary, hprod]
    exact MonoidHom.mem_ker.mp hendpoint
  obtain ⟨nextKernel, nextWord, hnextKernel, hnextProd,
      hnextLetters, hnextLength, hnextGeodesic⟩ :=
    exists_shorter_kernelGeodesic_of_relativeDiagramCertificate D hsc
      hmu hrho data.certificate q hq hker hboundary
  have hnextLength' : nextWord.length < word.length := by
    have hboundaryWord : data.certificate.boundaryWord = word :=
      data.certificate.boundaryWord_eq.trans data.diagram_boundary
    rw [hboundaryWord] at hnextLength
    exact hnextLength
  have hnextGeodesic' : nextWord.length = wordDist
      (D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation).alphabet.carrier 1
      nextWord.prod := by
    rw [hnextProd]
    exact hnextGeodesic
  let nextArea := nextWord.length
  have hnextArea : nextArea < area := by
    dsimp [nextArea]
    exact lt_of_lt_of_le hnextLength' (by omega)
  have hnextWordArea : nextWord.length = nextArea := by rfl
  refine ⟨{
    nextWord := nextWord
    next_word_letters := hnextLetters
    nextKernel := nextKernel
    next_kernel_mem := hnextKernel
    next_word_prod_eq := hnextProd
    next_word_geodesic := hnextGeodesic'
    next_area := nextArea
    next_area_lt := hnextArea
    next_word_area := hnextWordArea
    prefix_transfer := ?_ }⟩
  intro hbound i hi
  exact data.prefix_transfer nextKernel nextWord hnextKernel hnextProd
    hnextLetters hnextLength' hnextGeodesic hbound i hi

/-- A family of explicit least-area diagrams and prefix calculations supplies
the complete cut-induction premise.  The proof is a direct constructor: each
area branch invokes the certificate cut theorem above, then stores the
strictly shorter word as the recursive branch. -/
theorem kernelGeodesicCutInductionAt_of_data
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hmu : mu ≤ 1 / 1000)
    (hrho : 20 * (eps + 1) ≤ rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (hker : q.ker =
      Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
    (hdata : ∃ M : ℕ, ∀ (area : ℕ) (endpoint : G), endpoint ∈ q.ker →
      ∀ word : List G,
        (∀ x ∈ word,
          x ∈ (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier) →
        word.prod = endpoint →
        word.length = wordDist
          (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier 1 endpoint →
        word.length = area → word.prod ≠ 1 →
        Nonempty (KernelGeodesicCutData D W eps rho mu hsc q M area word)) :
    KernelGeodesicCutInductionAt D W eps rho mu hsc q := by
  obtain ⟨M, hM⟩ := hdata
  refine ⟨M, ?_⟩
  intro area endpoint hendpoint word hword hprod hgeodesic harea hne
  obtain ⟨data⟩ := hM area endpoint hendpoint word hword hprod hgeodesic
    harea hne
  exact kernelGeodesicCutStep_of_data D W eps rho mu hsc hmu hrho q hq M area
    endpoint word hendpoint hword hprod hgeodesic harea hne data hker

/-! ## The explicit measure check -/

/-- The zero-area branch of the construction has no nontrivial geodesic
boundary, so its witness is the exact zero constant. -/
theorem kernelGeodesicCutData_zero_measure_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (_hsc : RelWord.IsLemma44Input D W eps mu rho) :
    ∀ (word : List PUnit), word.length = 0 → word.prod ≠ 1 → False := by
  intro word hlength hne
  have hnil : word = [] := List.length_eq_zero_iff.mp hlength
  subst word
  exact hne (Subsingleton.elim _ _)

end HullSC
end GroupApproximation
