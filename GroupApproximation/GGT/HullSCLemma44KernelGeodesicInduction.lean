import GroupApproximation.GGT.HullSCLemma44KernelAssembly

/-!
# Area induction for the kernel-geodesic estimate

Osin's kernel-geodesic argument cuts a least-area relative diagram and then
repeats the argument on the strictly smaller diagram.  This file exposes the
well-founded part of that proof independently of the planar implementation.
`KernelGeodesicCutStep` is the exact local output needed by one cut: a smaller
area word with the same quotient endpoint and a transfer of the prefix bound.
`kernelGeodesicEstimateAt_of_cutInduction` proves the full uniform estimate by
strong induction on the explicit natural-number area measure.  The vk lane
can instantiate the local cut statement from its certificate and its diagram
area.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

/-! ## One area-cut step -/

/-- The local output of one least-area cut for an old-alphabet geodesic ending
in the filling kernel.  `next_area_lt` is the well-founded measure, while
`prefix_transfer` is the geometric part: a bound for all prefixes of the
smaller word bounds all prefixes of the current word with the same `M`. -/
structure KernelGeodesicCutStep
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (M : ℕ) (area : ℕ) (word : List G) where
  /-- The boundary word after the selected cell has been cut. -/
  nextWord : List G
  /-- The new word still uses the prefix-enlarged alphabet. -/
  next_word_letters : ∀ x ∈ nextWord,
    x ∈ (D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).alphabet.carrier
  /-- The cut has a new endpoint in the filling kernel.  A relator cut
  preserves the quotient endpoint, not the source-group endpoint. -/
  nextKernel : G
  next_kernel_mem : nextKernel ∈ q.ker
  next_word_prod_eq : nextWord.prod = nextKernel
  /-- The recursive boundary is geodesic in the prefix alphabet. -/
  next_word_geodesic : nextWord.length = wordDist
    (D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).alphabet.carrier 1 nextWord.prod
  /-- The explicit diagram area decreases at this cut. -/
  next_area : ℕ
  next_area_lt : next_area < area
  /-- The recursive word has the next diagram area as its length measure. -/
  next_word_area : nextWord.length = next_area
  /-- A bound on every recursive prefix transfers to the current word. -/
  prefix_transfer :
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

/-! ## The strictly smaller induction premise -/

/-- Every nontrivial kernel geodesic admits one area-decreasing cut.  This is
strictly local: it asks only for the next word, its smaller area, and the
prefix transfer used by the induction theorem below. -/
def KernelGeodesicCutInductionAt
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) : Prop :=
  ∃ M : ℕ, ∀ (area : ℕ) (k : G), k ∈ q.ker →
    ∀ word : List G,
      (∀ x ∈ word,
        x ∈ (D.adjoinRelatorPrefixes W
          hsc.toIsSmallCancellation).alphabet.carrier) →
      word.prod = k →
      word.length = wordDist
        (D.adjoinRelatorPrefixes W
          hsc.toIsSmallCancellation).alphabet.carrier 1 k →
      word.length = area → word.prod ≠ 1 →
      Nonempty (KernelGeodesicCutStep D W eps rho mu hsc q M area word)

/-! ## Strong induction on the explicit area -/

/-- The area-cut premise proves the old-geodesic estimate consumed by the
kernel-cone enlargement.  The proof uses strong induction on `area`; the
zero-area branch is closed by the geodesic length equation. -/
theorem kernelGeodesicEstimateAt_of_cutInduction
    {G : Type u} [Group G] {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q)
    (hcuts : KernelGeodesicCutInductionAt D W eps rho mu hsc q) :
    KernelGeodesicEstimateAt D W eps rho mu hsc q := by
  obtain ⟨M, hM⟩ := hcuts
  refine ⟨M, ?_⟩
  intro k hk word hword hprod hlength i hi
  let E := D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation
  let B := E.adjoinKernel q
  let P : ℕ → Prop := fun area =>
    ∀ (endpoint : G), endpoint ∈ q.ker → ∀ (word : List G),
      word.length = area →
      (∀ x ∈ word, x ∈ E.alphabet.carrier) →
      word.prod = endpoint →
      word.length = wordDist E.alphabet.carrier 1 endpoint →
      ∀ j ≤ word.length,
        wordDist B.alphabet.carrier 1 (word.take j).prod ≤ M
  have hP : ∀ area : ℕ, P area := by
    intro area
    induction area using Nat.strong_induction_on with
    | _ area ih =>
      intro endpoint hendpoint current hcurrentLength hcurrentLetters
        hcurrentProd hcurrentGeodesic j hj
      by_cases hone : current.prod = 1
      · have hkone : endpoint = 1 := by
          rw [← hcurrentProd, hone]
        have hzero : current.length = 0 := by
          rw [hcurrentGeodesic, hkone, wordDist_self]
        have hjzero : j = 0 := by omega
        subst hjzero
        have hnil : current = [] := List.length_eq_zero_iff.mp hzero
        subst current
        simp only [List.take_zero, List.prod_nil, wordDist_self]
        exact Nat.zero_le _
      · obtain ⟨C⟩ := hM area endpoint hendpoint current hcurrentLetters
          hcurrentProd hcurrentGeodesic hcurrentLength hone
        have hnextLength : C.nextWord.length = C.next_area :=
          C.next_word_area
        have hnextArea : C.next_area < area := C.next_area_lt
        have hnextLetters : ∀ x ∈ C.nextWord, x ∈ E.alphabet.carrier :=
          C.next_word_letters
        have hnextProd : C.nextWord.prod = C.nextKernel :=
          C.next_word_prod_eq
        have hnextGeodesic : C.nextWord.length =
            wordDist E.alphabet.carrier 1 C.nextKernel := by
          calc
            C.nextWord.length = wordDist E.alphabet.carrier 1 C.nextWord.prod :=
              C.next_word_geodesic
            _ = wordDist E.alphabet.carrier 1 C.nextKernel := by rw [hnextProd]
        have hnextBound : ∀ l ≤ C.nextWord.length,
            wordDist B.alphabet.carrier 1
              (C.nextWord.take l).prod ≤ M := by
          exact ih C.next_area hnextArea C.nextKernel C.next_kernel_mem
            C.nextWord hnextLength hnextLetters hnextProd hnextGeodesic
        exact C.prefix_transfer hnextBound j hj
  have hbound : ∀ j ≤ word.length,
      wordDist B.alphabet.carrier 1 (word.take j).prod ≤ M := by
    exact hP word.length k hk word rfl hword hprod hlength
  exact hbound i hi

/-! ## Uniform statement and model checks -/

/-- The cut-induction theorem supplies the complete uniform kernel-geodesic
statement required by the canonical assembly. -/
theorem kernelGeodesicEstimateStatement_of_cutInduction
    (hcuts : ∀ {G : Type u} [Group G] {Lambda : Type w}
      (D : GGT.RelGenSet G Lambda)
      (W : Set (List (GGT.RelLetter G Lambda)))
      (eps rho : ℕ) (mu : ℝ)
      (hsc : RelWord.IsLemma44Input D W eps mu rho)
      {Q : Type v} [Group Q] (q : G →* Q)
      (_hq : Function.Surjective q)
      (_hker : q.ker =
        Subgroup.normalClosure (GGT.RelLetter.listVal '' W))
      (_hcert : ∀ (R : ℕ) (Z : RelativeReducedDiagram D W R),
        Nonempty (RelativeDiagramCertificate D W eps mu Z)),
      KernelGeodesicCutInductionAt D W eps rho mu hsc q) :
    KernelGeodesicEstimateStatement.{u, v, w} := by
  refine ⟨?_⟩
  intro G _ Lambda D W eps rho mu hsc Q _ q hq hker hcert
  exact kernelGeodesicEstimateAt_of_cutInduction D W eps rho mu hsc q
    (hcuts D W eps rho mu hsc q hq hker hcert)

/-- At a one-point source the cut premise is witnessed by `M = 0` exactly:
there is no nontrivial boundary word on which a cut could be requested. -/
theorem kernelGeodesicCutInductionAt_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : PUnit →* Q) :
    KernelGeodesicCutInductionAt D W eps rho mu hsc q := by
  refine ⟨0, ?_⟩
  intro area k hk word hword hprod hlength harea hone
  have htrivial : word.prod = 1 := Subsingleton.elim _ _
  exact (hone htrivial).elim

/-- The one-point kernel-geodesic estimate has witness `M = 0` by equality. -/
theorem kernelGeodesicEstimateAt_trivialModel_zero
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : PUnit →* Q)
    (_hq : Function.Surjective q) :
    ∃ M : ℕ, M = 0 ∧
      ∀ k ∈ q.ker, ∀ word : List PUnit,
        (∀ x ∈ word,
          x ∈ (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier) →
        word.prod = k →
        word.length = wordDist
          (D.adjoinRelatorPrefixes W
            hsc.toIsSmallCancellation).alphabet.carrier 1 k →
        ∀ i ≤ word.length,
          wordDist
            ((D.adjoinRelatorPrefixes W
              hsc.toIsSmallCancellation).adjoinKernel q).alphabet.carrier
            1 (word.take i).prod ≤ M := by
  refine ⟨0, rfl, ?_⟩
  intro k hk word hword hprod hlength i hi
  have hkone : k = 1 := Subsingleton.elim _ _
  have hzero : word.length = 0 := by
    rw [hlength, hkone, wordDist_self]
  have hizero : i = 0 := by omega
  subst hizero
  have hnil : word = [] := List.length_eq_zero_iff.mp hzero
  subst word
  simp only [List.take_zero, List.prod_nil, wordDist_self]
  exact le_rfl

end HullSC
end GroupApproximation
