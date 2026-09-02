import GroupApproximation.GGT.HullSCLemma44KernelCone

/-!
# Kernel geodesics in Hull Lemma 4.4

Osin's proof of Theorem 4.1 applies Lemma 5.5 after enlarging the relative
generating set first by relator prefixes and then by the filling kernel.  This
file isolates the precise estimate needed by that application.  An old
geodesic ending at a kernel element must stay uniformly bounded in the
kernel-enlarged metric.

The source prefix graph is already hyperbolic by
`exists_hyperbolic_adjoinRelatorPrefixes`.  The theorem below checks every
other clause of Osin's Lemma 5.5, including the old base and peripheral
letters.  A second theorem adds the relative-ball finiteness clause and gives
the exact prefix-kernel conclusion consumed by Hull's quotient construction.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## Elementary bounds after adjoining the kernel -/

/-- A word over the prefix alphabet remains a word after the kernel is added. -/
theorem isWord_adjoinKernel_of_isWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (E : GGT.RelGenSet G Lambda) (q : G →* Q)
    {word : List G} {g : G} (hword : IsWord E.alphabet.carrier word g) :
    IsWord (E.adjoinKernel q).alphabet.carrier word g := by
  exact ⟨fun x hx => GGT.RelGenSet.alphabet_subset_adjoinKernel E q
    (hword.letters x hx), hword.prod_eq⟩

/-- Every prefix of an old-alphabet word has kernel-cone distance at most its
index. -/
theorem wordDist_adjoinKernel_prod_take_le
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (E : GGT.RelGenSet G Lambda) (q : G →* Q)
    (word : List G)
    (hword : ∀ x ∈ word, x ∈ E.alphabet.carrier) (i : ℕ) :
    wordDist (E.adjoinKernel q).alphabet.carrier 1
      (word.take i).prod ≤ i := by
  have htake : IsWord E.alphabet.carrier (word.take i)
      (word.take i).prod :=
    ⟨fun x hx => hword x (List.take_subset i word hx), rfl⟩
  have htakeCone : IsWord (E.adjoinKernel q).alphabet.carrier
      (word.take i) (word.take i).prod :=
    isWord_adjoinKernel_of_isWord E q htake
  have hlength := wordNorm_le_length htakeCone
  rw [wordDist_one_left, List.length_take] at hlength
  exact le_trans hlength (min_le_left _ _)

/-- A shortest old-alphabet word ending at an old letter has length at most
one. -/
theorem length_le_one_of_geodesic_to_oldLetter
    {G : Type u} [Group G] {Lambda : Type w}
    (E : GGT.RelGenSet G Lambda) {b : G} (hb : b ∈ E.alphabet.carrier)
    (word : List G)
    (hlength : word.length = wordDist E.alphabet.carrier 1 b) :
    word.length ≤ 1 := by
  have hnorm : wordNorm E.alphabet.carrier b ≤ 1 :=
    wordNorm_le_one_of_mem hb
  rw [wordDist_one_left] at hlength
  omega

/-! ## Osin Lemma 5.5 for the prefix-kernel graph -/

/-- The kernel-geodesic estimate gives hyperbolicity after adjoining the
kernel to the prefix generating set.

This is the Lemma 5.5 step in Osin's proof of Theorem 4.1.  The bound is only
requested for new kernel letters.  Old base and peripheral letters have old
distance at most one, so their geodesics satisfy the criterion automatically.
-/
theorem exists_hyperbolic_prefixKernelCone_of_kernelGeodesicBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (M : ℕ)
    (hkernel : ∀ k ∈ q.ker,
      ∀ word : List G,
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
            1 (word.take i).prod ≤ M) :
    ∃ delta : ℝ, IsHyperbolicSpace delta
      (Cayley ((D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).adjoinKernel q).alphabet) := by
  let E := D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation
  obtain ⟨delta, hdelta⟩ :=
    exists_hyperbolic_adjoinRelatorPrefixes D hD W hsc
  have hsub : E.alphabet.carrier ⊆
      (E.adjoinKernel q).alphabet.carrier :=
    GGT.RelGenSet.alphabet_subset_adjoinKernel E q
  refine GGT.OsinEnlargement.osinLemma55 G E.alphabet
    (E.adjoinKernel q).alphabet hsub delta hdelta (M + 1) ?_
  intro b hb word hword hprod hlength i hi
  rcases hb with hbBase | hbPeripheral
  · rcases hbBase with hbOldBase | hbKernel
    · have hbOld : b ∈ E.alphabet.carrier :=
        Set.mem_union_left _ hbOldBase
      have hwordLength : word.length ≤ 1 :=
        length_le_one_of_geodesic_to_oldLetter E hbOld word hlength
      have hprefix : wordDist (E.adjoinKernel q).alphabet.carrier 1
          (word.take i).prod ≤ i :=
        wordDist_adjoinKernel_prod_take_le E q word hword i
      omega
    · have hbound : wordDist (E.adjoinKernel q).alphabet.carrier 1
          (word.take i).prod ≤ M :=
        hkernel b hbKernel word hword hprod hlength i hi
      omega
  · have hbOld : b ∈ E.alphabet.carrier :=
      Set.mem_union_right _ hbPeripheral
    have hwordLength : word.length ≤ 1 :=
      length_le_one_of_geodesic_to_oldLetter E hbOld word hlength
    have hprefix : wordDist (E.adjoinKernel q).alphabet.carrier 1
        (word.take i).prod ≤ i :=
      wordDist_adjoinKernel_prod_take_le E q word hword i
    omega

/-! ## Hyperbolic embeddedness from the two exact estimates -/

/-- The kernel-geodesic bound and finite kernel-cone relative balls give the
prefix-kernel transfer used by Hull's quotient construction. -/
theorem isHyperbolicallyEmbedded_prefixKernelCone_of_bounds
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (M : ℕ)
    (hkernel : ∀ k ∈ q.ker,
      ∀ word : List G,
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
            1 (word.take i).prod ≤ M)
    (hloc : ∀ (lam : Lambda) (n : ℕ),
      (((D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).adjoinKernel q).relBall lam n).Finite) :
    ((D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).adjoinKernel q).IsHyperbolicallyEmbedded :=
  ⟨exists_hyperbolic_prefixKernelCone_of_kernelGeodesicBound
      D hD W hsc q M hkernel, hloc⟩

/-- The two estimates also give hyperbolic embeddedness of the concrete image
family in the quotient. -/
theorem isHyperbolicallyEmbedded_prefixQuotient_of_bounds
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) (M : ℕ)
    (hkernel : ∀ k ∈ q.ker,
      ∀ word : List G,
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
            1 (word.take i).prod ≤ M)
    (hloc : ∀ (lam : Lambda) (n : ℕ),
      (((D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).adjoinKernel q).relBall lam n).Finite) :
    (D.prefixQuotient W hsc.toIsSmallCancellation q hq).
      IsHyperbolicallyEmbedded := by
  apply isHyperbolicallyEmbedded_prefixQuotient_of_kernelConeTransfer
    D W hsc q hq
  exact isHyperbolicallyEmbedded_prefixKernelCone_of_bounds
    D hD W hsc q M hkernel hloc

end HullSC
end GroupApproximation
