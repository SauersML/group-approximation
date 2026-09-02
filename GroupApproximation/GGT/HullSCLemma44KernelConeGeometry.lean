import GroupApproximation.GGT.HullSCLemma44KernelCone

/-!
# Geometric estimates for the kernel cone in Hull's Lemma 4.4

Osin's proof of Theorem 5.4 separates the geometry of an enlarged relative
base into Lemmas 5.5, 5.6, and 5.8.  Lemma 5.5 is already proved in
`GuessingGeodesicsCriterion`: hyperbolicity survives an alphabet enlargement
when old geodesics ending at new letters remain uniformly bounded in the new
metric.  For the kernel cone, only the new kernel letters need an estimate;
old letters give a bound of one directly.

This file makes that reduction and also isolates the properness estimate from
Osin Lemma 5.8.  A uniform pullback of kernel-cone relative balls to relative
balls for the original family transfers local finiteness immediately.  Applied
to the prefix enlargement, the two estimates imply
`PrefixKernelConeTransferStatement`, which is the geometric input consumed by
the canonical Hull Lemma 4.4 assembly.

The two remaining pointwise statements are smaller than the quotient theorem:
`PrefixKernelGeodesicTransferAt` asks only for the Lemma 5.6 geodesic bound,
and `PrefixKernelPeripheralTransferAt` asks only for the Lemma 5.8 relative-ball
bound.  Both take the already-proved linear kernel area as their diagrammatic
input.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## The bounded-geodesic estimate -/

/-- Old geodesics ending at kernel elements remain uniformly bounded in the
kernel-cone metric.  This is the kernel-letter part of Osin Lemma 5.6. -/
def KernelGeodesicBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (E : GGT.RelGenSet G Lambda) (q : G →* Q) : Prop :=
  ∃ M : ℕ, ∀ b ∈ q.ker,
    ∀ word : List G, (∀ x ∈ word, x ∈ E.alphabet.carrier) →
      word.prod = b →
      word.length = wordDist E.alphabet.carrier 1 b →
        ∀ i ≤ word.length,
          wordDist (E.adjoinKernel q).alphabet.carrier 1
            (word.take i).prod ≤ M

/-- A prefix of an old-alphabet word has kernel-cone distance at most its
prefix length. -/
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
  have hold : wordNorm E.alphabet.carrier (word.take i).prod ≤
      (word.take i).length := wordNorm_le_length htake
  have hnew : wordNorm (E.adjoinKernel q).alphabet.carrier
      (word.take i).prod ≤
      wordNorm E.alphabet.carrier (word.take i).prod :=
    wordNorm_mono (GGT.RelGenSet.alphabet_subset_adjoinKernel E q)
      (wordLengths_nonempty E.alphabet.symmetricGenerating _)
  rw [wordDist_one_left]
  exact le_trans hnew (le_trans hold (by rw [List.length_take]; omega))

/-- A kernel-letter bound extends to the full enlarged alphabet: an old
letter is the endpoint of an old geodesic of length at most one. -/
theorem exists_fullGeodesicBound_adjoinKernel
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (E : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hbound : KernelGeodesicBound E q) :
    ∃ M : ℕ, ∀ b ∈ (E.adjoinKernel q).alphabet.carrier,
      ∀ word : List G, (∀ x ∈ word, x ∈ E.alphabet.carrier) →
        word.prod = b →
        word.length = wordDist E.alphabet.carrier 1 b →
          ∀ i ≤ word.length,
            wordDist (E.adjoinKernel q).alphabet.carrier 1
              (word.take i).prod ≤ M := by
  obtain ⟨M, hM⟩ := hbound
  refine ⟨M + 1, ?_⟩
  intro b hb word hword hprod hlength i hi
  rcases hb with hb | hb
  · rcases hb with hb | hb
    · have hbOld : b ∈ E.alphabet.carrier := Set.mem_union_left _ hb
      have hnorm : wordNorm E.alphabet.carrier b ≤ 1 :=
        wordNorm_le_one_of_mem hbOld
      have hwordLength : word.length ≤ 1 := by
        rw [wordDist_one_left] at hlength
        omega
      have hprefix := wordDist_adjoinKernel_prod_take_le E q word hword i
      omega
    · exact le_trans (hM b hb word hword hprod hlength i hi)
        (Nat.le_add_right M 1)
  · have hbOld : b ∈ E.alphabet.carrier := Set.mem_union_right _ hb
    have hnorm : wordNorm E.alphabet.carrier b ≤ 1 :=
      wordNorm_le_one_of_mem hbOld
    have hwordLength : word.length ≤ 1 := by
      rw [wordDist_one_left] at hlength
      omega
    have hprefix := wordDist_adjoinKernel_prod_take_le E q word hword i
    omega

/-- Osin Lemma 5.5 converts the kernel-letter bound into hyperbolicity of the
kernel-coned Cayley graph. -/
theorem exists_hyperbolic_adjoinKernel_of_geodesicBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (E : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley E.alphabet))
    (q : G →* Q) (hbound : KernelGeodesicBound E q) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (E.adjoinKernel q).alphabet) := by
  obtain ⟨delta, hdelta⟩ := hhyper
  obtain ⟨M, hM⟩ := exists_fullGeodesicBound_adjoinKernel E q hbound
  exact GGT.OsinEnlargement.osinLemma55 G E.alphabet
    (E.adjoinKernel q).alphabet
      (GGT.RelGenSet.alphabet_subset_adjoinKernel E q)
        delta hdelta M hM

/-! ## The relative-ball estimate -/

/-- Every kernel-cone relative ball is contained in a uniformly bounded
relative ball for the original relative generating set.  This is the form of
Osin Lemma 5.8 used for the prefix enlargement. -/
def PrefixKernelPeripheralPullbackBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (radius : ℕ → ℕ) : Prop :=
  ∀ (lam : Lambda) (n : ℕ),
    (((D.adjoinRelatorPrefixes W hsc).adjoinKernel q).relBall lam n) ⊆
      D.relBall lam (radius n)

/-- A prefix kernel-cone pullback bound transfers source local finiteness. -/
theorem locallyFinite_prefixKernelCone_of_pullbackBound
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (radius : ℕ → ℕ)
    (hpull : PrefixKernelPeripheralPullbackBound D W hsc q radius) :
    ∀ (lam : Lambda) (n : ℕ),
      (((D.adjoinRelatorPrefixes W hsc).adjoinKernel q).relBall lam n).Finite := by
  intro lam n
  exact (hD.locallyFinite lam (radius n)).subset (hpull lam n)

/-! ## Pointwise forms of Osin Lemmas 5.6 and 5.8 -/

/-- The Lemma 5.6 estimate at one source relative generating set. -/
def PrefixKernelGeodesicTransferAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) : Prop :=
  ∀ (W : Set (List (GGT.RelLetter G Lambda))) (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : G →* Q) (_ : Function.Surjective q),
      RelativeLinearKernelArea D W q →
        KernelGeodesicBound
          (D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation) q

/-- The Lemma 5.8 estimate at one source relative generating set. -/
def PrefixKernelPeripheralTransferAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) : Prop :=
  ∀ (W : Set (List (GGT.RelLetter G Lambda))) (eps rho : ℕ) (mu : ℝ)
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {Q : Type v} [Group Q] (q : G →* Q) (_ : Function.Surjective q),
      RelativeLinearKernelArea D W q →
        ∃ radius : ℕ → ℕ,
          PrefixKernelPeripheralPullbackBound D W
            hsc.toIsSmallCancellation q radius

/-- Uniform form of the Lemma 5.6 kernel-geodesic estimate. -/
def PrefixKernelGeodesicTransferStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded → PrefixKernelGeodesicTransferAt.{u, v, w} D

/-- Uniform form of the Lemma 5.8 kernel-peripheral estimate. -/
def PrefixKernelPeripheralTransferStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda),
    D.IsHyperbolicallyEmbedded → PrefixKernelPeripheralTransferAt.{u, v, w} D

/-- The two pointwise estimates, source prefix hyperbolicity, and Osin Lemma
5.5 give the complete prefix kernel-cone transfer. -/
theorem prefixKernelConeTransferStatement_of_geodesic_of_peripheral
    (hgeo : PrefixKernelGeodesicTransferStatement.{u, v, w})
    (hper : PrefixKernelPeripheralTransferStatement.{u, v, w}) :
    PrefixKernelConeTransferStatement.{u, v, w} := by
  intro G _ Lambda D hD W eps rho mu hsc Q _ q hq harea
  let E := D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation
  have hgeoBound : KernelGeodesicBound E q :=
    hgeo D hD W eps rho mu hsc q hq harea
  have hprefixHyper : ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley E.alphabet) :=
    exists_hyperbolic_adjoinRelatorPrefixes D hD W hsc
  have hconeHyper : ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (E.adjoinKernel q).alphabet) :=
    exists_hyperbolic_adjoinKernel_of_geodesicBound E hprefixHyper q hgeoBound
  obtain ⟨radius, hpull⟩ := hper D hD W eps rho mu hsc q hq harea
  have hconeLocal : ∀ (lam : Lambda) (n : ℕ),
      ((E.adjoinKernel q).relBall lam n).Finite :=
    locallyFinite_prefixKernelCone_of_pullbackBound D hD W
      hsc.toIsSmallCancellation q radius hpull
  exact ⟨hconeHyper, hconeLocal⟩

/-! ## Model tests -/

/-- The kernel-geodesic bound holds with constant zero on the one-point
source group. -/
theorem kernelGeodesicBound_trivialModel
    {Q : Type v} [Group Q] {Lambda : Type w}
    (E : GGT.RelGenSet PUnit Lambda) (q : PUnit →* Q) :
    KernelGeodesicBound E q := by
  refine ⟨0, ?_⟩
  intro b hb word hword hprod hlength i hi
  have hone : (word.take i).prod = 1 := Subsingleton.elim _ _
  rw [hone, wordDist_self]

/-- The peripheral pullback bound holds with radius zero on the one-point
source group. -/
theorem prefixKernelPeripheralPullbackBound_trivialModel
    {Q : Type v} [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet PUnit Lambda)
    (W : Set (List (GGT.RelLetter PUnit Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : PUnit →* Q) :
    PrefixKernelPeripheralPullbackBound D W hsc q (fun _ => 0) := by
  intro lam n x hx
  rw [GGT.RelGenSet.relBall_zero]
  exact Set.mem_singleton_iff.mpr (Subsingleton.elim _ _)

/-- The full pointwise Lemma 5.6 interface has the one-point source model. -/
theorem prefixKernelGeodesicTransferAt_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    PrefixKernelGeodesicTransferAt.{0, v, w} D := by
  intro W eps rho mu hsc Q _ q _ harea
  exact kernelGeodesicBound_trivialModel
    (D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation) q

/-- The full pointwise Lemma 5.8 interface has the one-point source model. -/
theorem prefixKernelPeripheralTransferAt_trivialModel
    {Lambda : Type w} (D : GGT.RelGenSet PUnit Lambda) :
    PrefixKernelPeripheralTransferAt.{0, v, w} D := by
  intro W eps rho mu hsc Q _ q _ harea
  exact ⟨fun _ => 0,
    prefixKernelPeripheralPullbackBound_trivialModel D W
      hsc.toIsSmallCancellation q⟩

end HullSC
end GroupApproximation
