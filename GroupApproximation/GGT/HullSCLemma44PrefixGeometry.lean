import GroupApproximation.GGT.CayleyFourPointConverse
import GroupApproximation.GGT.GuessingGeodesicsCriterion
import GroupApproximation.GGT.HullSCConeOffHeavyChordChain
import GroupApproximation.GGT.HullSCLemma44PrefixPresentation

/-!
# Hyperbolicity after adjoining relator prefixes

The prefix base used for unbounded relator families is an infinite alphabet
enlargement, so its hyperbolicity is not automatic.  Osin's Lemma 5.5 gives
the needed criterion: every geodesic in the old alphabet whose endpoint is a
new letter must remain uniformly bounded in the enlarged metric.

For a relator prefix, `IsLemma44Input.quasiGeodesic` supplies a `(4,1)` chain
from the identity to that prefix.  The proved Morse lemma puts every point of
an old geodesic chord near one of the chain vertices.  Every chain vertex is
itself a relator prefix, hence a single letter of the enlarged alphabet.  The
required bound is the Morse constant plus one.

This proves the hyperbolicity clause for the prefix enlargement in the source
group.  The quotient bridge also has to control the filling kernel and the
transported peripheral metrics; those are kept separate in
`HullSCLemma44RelativeIsoperimetric`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Elementary prefix facts -/

/-- The old full relative alphabet is contained in the prefix-enlarged one. -/
theorem alphabet_subset_adjoinRelatorPrefixes
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
    D.alphabet.carrier ⊆
      (D.adjoinRelatorPrefixes W hsc).alphabet.carrier := by
  rintro x (hx | hx)
  · exact Set.mem_union_left _ (Set.mem_union_left _ hx)
  · exact Set.mem_union_right _ hx

/-- A prefix of an old-alphabet word has enlarged distance at most its prefix
length. -/
theorem wordDist_adjoinRelatorPrefixes_prod_take_le
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (word : List G)
    (hword : ∀ x ∈ word, x ∈ D.alphabet.carrier) (i : ℕ) :
    wordDist (D.adjoinRelatorPrefixes W hsc).alphabet.carrier 1
      (word.take i).prod ≤ i := by
  let E := D.adjoinRelatorPrefixes W hsc
  have hsub : D.alphabet.carrier ⊆ E.alphabet.carrier :=
    alphabet_subset_adjoinRelatorPrefixes D W hsc
  have htake : IsWord D.alphabet.carrier (word.take i)
      (word.take i).prod :=
    ⟨fun x hx => hword x (List.take_subset i word hx), rfl⟩
  have hold : wordNorm D.alphabet.carrier (word.take i).prod ≤
      (word.take i).length := wordNorm_le_length htake
  have hnew : wordNorm E.alphabet.carrier (word.take i).prod ≤
      wordNorm D.alphabet.carrier (word.take i).prod :=
    wordNorm_mono hsub
      (wordLengths_nonempty D.alphabet.symmetricGenerating _)
  rw [wordDist_one_left]
  exact le_trans hnew (le_trans hold (by rw [List.length_take]; omega))

/-- Restrict the stored relator quasi-geodesic chain to a displayed prefix. -/
theorem isQuasiGeodesicChainAt_prefix
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    {word pre suffix : List (GGT.RelLetter G Lambda)}
    (hword : word ∈ W) (hsplit : word = pre ++ suffix) :
    GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      (fun i => GGT.RelLetter.listVal (pre.take i)) pre.length := by
  intro i j hij hj
  have hpreLength : pre.length ≤ word.length := by
    rw [hsplit, List.length_append]
    omega
  have hfull := hsc.quasiGeodesic word hword i j hij
    (le_trans hj hpreLength)
  have hi : word.take i = pre.take i := by
    rw [hsplit, List.take_append_of_le_length (le_trans hij hj)]
  have hj' : word.take j = pre.take j := by
    rw [hsplit, List.take_append_of_le_length hj]
  simpa only [hi, hj'] using hfull

/-- Every vertex of a displayed prefix chain is again a prefix value. -/
theorem listVal_take_mem_prefixValues
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {word pre suffix : List (GGT.RelLetter G Lambda)}
    (hword : word ∈ W) (hsplit : word = pre ++ suffix)
    (i : ℕ) :
    GGT.RelLetter.listVal (pre.take i) ∈ RelWord.prefixValues W := by
  apply RelWord.listVal_mem_prefixValues (pre := pre.take i)
    (suffix := pre.drop i ++ suffix) hword
  calc
    word = pre ++ suffix := hsplit
    _ = (pre.take i ++ pre.drop i) ++ suffix := by
      rw [List.take_append_drop]
    _ = pre.take i ++ (pre.drop i ++ suffix) := List.append_assoc _ _ _

/-! ## Osin's bounded-geodesic condition -/

/-- Old geodesics ending at a relator-prefix value stay uniformly bounded in
the prefix-enlarged metric. -/
theorem exists_prefixGeodesicBound
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho) :
    ∃ M : ℕ, ∀ b ∈ (D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).alphabet.carrier,
      ∀ word : List G, (∀ x ∈ word, x ∈ D.alphabet.carrier) →
        word.prod = b →
        word.length = wordDist D.alphabet.carrier 1 b →
          ∀ i ≤ word.length,
            wordDist (D.adjoinRelatorPrefixes W
              hsc.toIsSmallCancellation).alphabet.carrier 1
                (word.take i).prod ≤ M := by
  obtain ⟨delta, hdelta⟩ := hD.hyperbolic
  have hfour : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier
      ⌈delta⌉₊ :=
    GGT.isFourPointHyperbolic_of_isHyperbolicSpace_cayley D.alphabet hdelta
  obtain ⟨R, hR⟩ :=
    exists_index_wordDist_le_of_isBetween_of_fourPoint 4 1 ⌈delta⌉₊
  let E := D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation
  have hsub : D.alphabet.carrier ⊆ E.alphabet.carrier :=
    alphabet_subset_adjoinRelatorPrefixes D W hsc.toIsSmallCancellation
  refine ⟨R + 1, ?_⟩
  intro b hb word hword hprod hlength i hi
  change wordDist E.alphabet.carrier 1 (word.take i).prod ≤ R + 1
  have hprefix : wordDist E.alphabet.carrier 1 (word.take i).prod ≤ i :=
    wordDist_adjoinRelatorPrefixes_prod_take_le D W
      hsc.toIsSmallCancellation word hword i
  rcases hb with hbbase | hbperipheral
  · rcases hbbase with hbold | hbprefix
    · have hbNorm : wordNorm D.alphabet.carrier b ≤ 1 :=
        wordNorm_le_one_of_mem (Set.mem_union_left _ hbold)
      rw [wordDist_one_left] at hlength
      omega
    · obtain ⟨relator, hrelator, pre, suffix, hsplit, rfl⟩ := hbprefix
      have hchainAt :=
        isQuasiGeodesicChainAt_prefix hsc hrelator hsplit
      have hchain : Hyperbolic.IsQuasiGeodesic D.alphabet.carrier 4 1
          pre.length (fun j => GGT.RelLetter.listVal (pre.take j)) :=
        hchainAt.toQuasiGeodesic_four
      have hgeo : IsGeodesicWord D.alphabet.carrier word
          (GGT.RelLetter.listVal pre) := by
        refine ⟨⟨hword, hprod⟩, ?_⟩
        rwa [wordDist_one_left] at hlength
      have hgeoSplit : IsGeodesicWord D.alphabet.carrier
          (word.take i ++ word.drop i)
          (word.take i ++ word.drop i).prod := by
        have hw : word.take i ++ word.drop i = word :=
          List.take_append_drop i word
        rw [hw]
        simpa only [hprod] using hgeo
      have hbetween : Hyperbolic.IsBetween D.alphabet.carrier 1
          (word.take i).prod (GGT.RelLetter.listVal pre) := by
        obtain ⟨hbetween, _⟩ := Hyperbolic.isBetween_of_geodesic_append
          D.alphabet.symmetricGenerating 1 hgeoSplit
        simpa only [one_mul, List.take_append_drop, hprod] using hbetween
      have hzero : GGT.RelLetter.listVal (pre.take 0) = 1 := rfl
      have hend : GGT.RelLetter.listVal (pre.take pre.length) =
          GGT.RelLetter.listVal pre := by rw [List.take_length]
      have hbetween' : Hyperbolic.IsBetween D.alphabet.carrier
          (GGT.RelLetter.listVal (pre.take 0)) (word.take i).prod
          (GGT.RelLetter.listVal (pre.take pre.length)) := by
        rwa [hzero, hend]
      obtain ⟨j, hj, hclose⟩ := hR G inferInstance D.alphabet.carrier
        D.alphabet.symmetricGenerating hfour pre.length
        (fun m => GGT.RelLetter.listVal (pre.take m)) hchain
          (word.take i).prod hbetween'
      have hjprefix : GGT.RelLetter.listVal (pre.take j) ∈
          RelWord.prefixValues W :=
        listVal_take_mem_prefixValues hrelator hsplit j
      have hjone : wordDist E.alphabet.carrier 1
          (GGT.RelLetter.listVal (pre.take j)) ≤ 1 := by
        rw [wordDist_one_left]
        exact wordNorm_le_one_of_mem (Set.mem_union_left _
          (Set.mem_union_right _ hjprefix))
      have hcloseNew : wordDist E.alphabet.carrier
          (GGT.RelLetter.listVal (pre.take j)) (word.take i).prod ≤ R := by
        exact le_trans
          (wordNorm_mono hsub
            (wordLengths_nonempty D.alphabet.symmetricGenerating _)) hclose
      have htriangle := wordDist_triangle E.alphabet.symmetricGenerating 1
        (GGT.RelLetter.listVal (pre.take j)) (word.take i).prod
      omega
  · have hbNorm : wordNorm D.alphabet.carrier b ≤ 1 :=
      wordNorm_le_one_of_mem (Set.mem_union_right _ hbperipheral)
    rw [wordDist_one_left] at hlength
    omega

/-! ## Hyperbolicity of the source prefix enlargement -/

/-- Adjoining all relator prefixes preserves hyperbolicity of the source
relative Cayley graph. -/
theorem exists_hyperbolic_adjoinRelatorPrefixes
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho) :
    ∃ delta' : ℝ, IsHyperbolicSpace delta'
      (Cayley (D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).alphabet) := by
  obtain ⟨delta, hdelta⟩ := hD.hyperbolic
  obtain ⟨M, hM⟩ := exists_prefixGeodesicBound D hD W hsc
  exact GGT.OsinEnlargement.osinLemma55 G D.alphabet
    (D.adjoinRelatorPrefixes W hsc.toIsSmallCancellation).alphabet
      (alphabet_subset_adjoinRelatorPrefixes D W hsc.toIsSmallCancellation)
        delta hdelta M hM

/-- Once local finiteness is supplied, the source prefix enlargement is a
hyperbolically embedded relative generating set. -/
theorem isHyperbolicallyEmbedded_adjoinRelatorPrefixes_of_locallyFinite
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input D W eps mu rho)
    (hloc : ∀ (lam : Lambda) (n : ℕ),
      ((D.adjoinRelatorPrefixes W
        hsc.toIsSmallCancellation).relBall lam n).Finite) :
    (D.adjoinRelatorPrefixes W
      hsc.toIsSmallCancellation).IsHyperbolicallyEmbedded :=
  ⟨exists_hyperbolic_adjoinRelatorPrefixes D hD W hsc, hloc⟩

end HullSC
end GroupApproximation
