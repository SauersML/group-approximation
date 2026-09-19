import GroupApproximation.GGT.DGOCorollary427PairLocal
import GroupApproximation.GGT.GeodesicChainThrough
import GroupApproximation.GGT.MorseLemmaDischarge

/-!
# DGO Corollary 4.27

Hyperbolic embeddedness is unchanged by a finite symmetric difference of the
relative base.

The local-finiteness half is
`RelGenSet.localFiniteness_iff_of_finite_symmDiff`.  This file supplies the
other half.  A finite change of alphabet gives a uniform bi-Lipschitz comparison
of the two word metrics.  A geodesic chain for the target metric is therefore a
quasi-geodesic for the source metric.  The proved discrete Morse lemma moves
its vertices to source between-points.  A first-crossing argument moves source
between-points back to target between-points.  Source slimness can then be read
as target slimness, hence as the target four-point condition.

This is the deletion direction which the monotone form of Osin's Lemma 5.5
cannot supply: adding finitely many bounded shortcuts preserves hyperbolicity
by that lemma, but removing them is a genuine quasi-isometry-invariance step.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

namespace FiniteChange

variable {G : Type u} [Group G]

/-! ## Finite changes give a bi-Lipschitz comparison -/

/-- A uniform bound on the `T`-length of the `S`-letters gives the corresponding
word-length comparison. -/
theorem wordNorm_le_mul_of_generator_bound {S T : Set G}
    (hS : IsSymmetricGeneratingSet S) (hT : IsSymmetricGeneratingSet T)
    {K : ℕ} (hK : ∀ s ∈ S, wordNorm T s ≤ K) (g : G) :
    wordNorm T g ≤ K * wordNorm S g := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq hS g
  have hbound : ∀ n ∈ l.map (wordNorm T), n ≤ K := by
    intro n hn
    simp only [List.mem_map] at hn
    obtain ⟨s, hs, rfl⟩ := hn
    exact hK s (hl.letters s hs)
  calc
    wordNorm T g = wordNorm T l.prod := by rw [hl.prod_eq]
    _ ≤ (l.map (wordNorm T)).sum := wordNorm_prod_le hT l
    _ ≤ (l.map (wordNorm T)).length * K := sum_le_length_mul _ _ hbound
    _ = K * wordNorm S g := by rw [List.length_map, hlen]; ring

/-- Finitely many `S`-letters outside `T` have a common `T`-length bound; the
letters already in `T` cost at most one. -/
theorem exists_generator_bound_of_finite_diff {S T : Set G}
    (hfin : (S \ T).Finite) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ s ∈ S, wordNorm T s ≤ K := by
  classical
  let K : ℕ := 1 + ∑ s ∈ hfin.toFinset, wordNorm T s
  refine ⟨K, by simp [K], ?_⟩
  intro s hs
  by_cases hsT : s ∈ T
  · exact (wordNorm_le_one_of_mem hsT).trans (by simp [K])
  · have hsfin : s ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hs, hsT⟩
    have hsum : wordNorm T s ≤ ∑ x ∈ hfin.toFinset, wordNorm T x :=
      Finset.single_le_sum (s := hfin.toFinset) (f := fun x => wordNorm T x)
        (fun _ _ => Nat.zero_le _) hsfin
    exact hsum.trans (by simp [K])

/-- Two symmetric generating sets with finite differences in both directions
have bi-Lipschitz word metrics. -/
theorem exists_bilipschitz_of_finite_diff {S T : Set G}
    (hS : IsSymmetricGeneratingSet S) (hT : IsSymmetricGeneratingSet T)
    (hSTfin : (S \ T).Finite) (hTSfin : (T \ S).Finite) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ x y : G,
      wordDist T x y ≤ K * wordDist S x y ∧
        wordDist S x y ≤ K * wordDist T x y := by
  obtain ⟨KST, -, hKST⟩ := exists_generator_bound_of_finite_diff hSTfin
  obtain ⟨KTS, -, hKTS⟩ := exists_generator_bound_of_finite_diff hTSfin
  let K : ℕ := max 1 (max KST KTS)
  refine ⟨K, le_max_left _ _, ?_⟩
  intro x y
  have hST := wordNorm_le_mul_of_generator_bound hS hT hKST (x⁻¹ * y)
  have hTS := wordNorm_le_mul_of_generator_bound hT hS hKTS (x⁻¹ * y)
  have hKSTK : KST ≤ K := by
    dsimp [K]
    exact (le_max_left KST KTS).trans (le_max_right 1 (max KST KTS))
  have hKTSK : KTS ≤ K := by
    dsimp [K]
    exact (le_max_right KST KTS).trans (le_max_right 1 (max KST KTS))
  constructor
  · exact hST.trans (Nat.mul_le_mul_right _ hKSTK)
  · exact hTS.trans (Nat.mul_le_mul_right _ hKTSK)

/-! ## Morse transport of hyperbolicity -/

/-- Two source between-points whose source parameters differ by at most `D`
are at most `D + 2δ` apart. -/
theorem wordDist_le_of_between_parameter_diff {S : Set G}
    (hS : IsSymmetricGeneratingSet S) {δ D : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ) {x z p q : G}
    (hp : Hyperbolic.IsBetween S x p z)
    (hq : Hyperbolic.IsBetween S x q z)
    (hpq : wordDist S x p ≤ wordDist S x q + D)
    (hqp : wordDist S x q ≤ wordDist S x p + D) :
    wordDist S p q ≤ D + 2 * δ := by
  have h4 := hδ x z p q
  have hp' : wordDist S x p + wordDist S p z = wordDist S x z := hp
  have hq' : wordDist S x q + wordDist S q z = wordDist S x z := hq
  have hzp : wordDist S z p = wordDist S p z := wordDist_comm hS z p
  have hzq : wordDist S z q = wordDist S q z := wordDist_comm hS z q
  have hmax : max (wordDist S x p + wordDist S z q)
      (wordDist S x q + wordDist S z p) ≤ wordDist S x z + D :=
    max_le (by omega) (by omega)
  omega

/-- A source between-point is uniformly close, in the target metric, to a
target between-point with the same endpoints.

Take a target geodesic chain.  It is a source quasi-geodesic by the
bi-Lipschitz comparison, so Morse projects each of its vertices to a source
between-point.  Stop at the first chain vertex whose source distance from the
first endpoint reaches the parameter of `r`.  Consecutive parameters move by
at most `K`; the Morse error is `R`; and the source four-point condition
compares the two source between-points. -/
theorem exists_target_between_near_source_between {S T : Set G}
    (hS : IsSymmetricGeneratingSet S) (hT : IsSymmetricGeneratingSet T)
    {K δ R : ℕ} (hK : 1 ≤ K)
    (hT_le : ∀ x y : G, wordDist T x y ≤ K * wordDist S x y)
    (hS_le : ∀ x y : G, wordDist S x y ≤ K * wordDist T x y)
    (hδ : Hyperbolic.IsFourPointHyperbolic S δ)
    (hMorse : ∀ (n : ℕ) (p : ℕ → G),
      Hyperbolic.IsQuasiGeodesic S K 0 n p → ∀ i ≤ n,
        ∃ q : G, Hyperbolic.IsBetween S (p 0) q (p n) ∧
          wordDist S (p i) q ≤ R)
    {x r z : G} (hr : Hyperbolic.IsBetween S x r z) :
    ∃ s : G, Hyperbolic.IsBetween T x s z ∧
      wordDist T r s ≤ K * (K + 2 * R + 2 * δ) := by
  obtain ⟨c, hc0, hcn, hc⟩ := exists_isGeodesicChain hT x z
  let n : ℕ := wordDist T x z
  have hcqg : Hyperbolic.IsQuasiGeodesic S K 0 n c := by
    intro i hi j hj hij
    have hcij : wordDist T (c i) (c j) = j - i := hc i j hij hj
    constructor
    · simpa [hcij] using hS_le (c i) (c j)
    · have h := hT_le (c i) (c j)
      rw [hcij] at h
      simpa using h
  have hproject : ∀ i ≤ n, ∃ q : G,
      Hyperbolic.IsBetween S x q z ∧ wordDist S (c i) q ≤ R := by
    intro i hi
    obtain ⟨q, hq, hd⟩ := hMorse n c hcqg i hi
    rw [hc0, hcn] at hq
    exact ⟨q, hq, hd⟩
  let a : ℕ := wordDist S x r
  by_cases haR : a ≤ R
  · refine ⟨x, Hyperbolic.isBetween_left T x z, ?_⟩
    have hrcomm : wordDist T r x = wordDist T x r := wordDist_comm hT r x
    rw [hrcomm]
    have ha : wordDist S x r ≤ K + 2 * R + 2 * δ := by
      dsimp [a] at haR ⊢
      omega
    exact (hT_le x r).trans (Nat.mul_le_mul_left K ha)
  · have hex : ∃ i : ℕ, i ≤ n ∧ a ≤ wordDist S x (c i) := by
      refine ⟨n, le_rfl, ?_⟩
      rw [hcn]
      have hr' : wordDist S x r + wordDist S r z = wordDist S x z := hr
      dsimp [a]
      omega
    let i : ℕ := Nat.find hex
    have hi : i ≤ n ∧ a ≤ wordDist S x (c i) := by
      dsimp [i]
      exact Nat.find_spec hex
    have hi0 : 0 < i := by
      by_contra hnot
      have hiEq : i = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hiEq, hc0, wordDist_self] at hi
      omega
    have hprevN : i - 1 ≤ n := by omega
    have hprev : wordDist S x (c (i - 1)) < a := by
      have hminimal : ¬ (i - 1 ≤ n ∧ a ≤ wordDist S x (c (i - 1))) :=
        Nat.find_min hex (by omega)
      have hnotle : ¬ a ≤ wordDist S x (c (i - 1)) :=
        fun hle => hminimal ⟨hprevN, hle⟩
      omega
    have hstepT : wordDist T (c (i - 1)) (c i) = 1 := by
      have hchain := hc (i - 1) i (by omega) hi.1
      convert hchain using 1; omega
    have hstepS : wordDist S (c (i - 1)) (c i) ≤ K := by
      have h := hS_le (c (i - 1)) (c i)
      rw [hstepT] at h
      simpa using h
    have hci : wordDist S x (c i) ≤ a + K := by
      have htri := wordDist_triangle hS x (c (i - 1)) (c i)
      omega
    obtain ⟨q, hq, hciq⟩ := hproject i hi.1
    have hpar1 : wordDist S x r ≤ wordDist S x q + (K + R) := by
      have hreach : wordDist S x r ≤ wordDist S x (c i) := by
        simpa [a] using hi.2
      have htri := wordDist_triangle hS x q (c i)
      have hcomm : wordDist S q (c i) = wordDist S (c i) q :=
        wordDist_comm hS q (c i)
      omega
    have hpar2 : wordDist S x q ≤ wordDist S x r + (K + R) := by
      have htri := wordDist_triangle hS x (c i) q
      dsimp [a] at hci ⊢
      omega
    have hrq : wordDist S r q ≤ K + R + 2 * δ :=
      wordDist_le_of_between_parameter_diff hS hδ hr hq hpar1 hpar2
    have hrc : wordDist S r (c i) ≤ K + 2 * R + 2 * δ := by
      have htri := wordDist_triangle hS r q (c i)
      have hcomm : wordDist S q (c i) = wordDist S (c i) q :=
        wordDist_comm hS q (c i)
      omega
    refine ⟨c i, ?_, (hT_le r (c i)).trans (Nat.mul_le_mul_left K hrc)⟩
    have hbet := hc.isBetween hi.1
    rwa [hc0, hcn] at hbet

/-- Hyperbolicity crosses a bi-Lipschitz change of word metric.  This is the
exact quasi-isometry-invariance consequence needed for finite alphabet
changes. -/
theorem exists_hyperbolic_of_bilipschitz (A B : Alphabet G) {K : ℕ}
    (hK : 1 ≤ K)
    (hB_le : ∀ x y : G,
      wordDist B.carrier x y ≤ K * wordDist A.carrier x y)
    (hA_le : ∀ x y : G,
      wordDist A.carrier x y ≤ K * wordDist B.carrier x y)
    {d : ℝ} (hA : IsHyperbolicSpace d (Cayley A)) :
    ∃ d' : ℝ, IsHyperbolicSpace d' (Cayley B) := by
  let δ : ℕ := ⌈d⌉₊
  have hfour : Hyperbolic.IsFourPointHyperbolic A.carrier δ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley A hA
  have hslim : Hyperbolic.IsSlimTriangles A.carrier (4 * δ) :=
    Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic A.symmetricGenerating hfour
  obtain ⟨R, hR⟩ := Hyperbolic.morseLemma_univ K 0 δ
  have hMorse : ∀ (n : ℕ) (p : ℕ → G),
      Hyperbolic.IsQuasiGeodesic A.carrier K 0 n p → ∀ i ≤ n,
        ∃ q : G, Hyperbolic.IsBetween A.carrier (p 0) q (p n) ∧
          wordDist A.carrier (p i) q ≤ R :=
    hR G inferInstance A.carrier A.symmetricGenerating hfour
  let D : ℕ := K * R + K * (4 * δ) + K * (K + 2 * R + 2 * δ)
  have hslimB : Hyperbolic.IsSlimTriangles B.carrier D := by
    intro x y z p hp
    obtain ⟨c, hc0, hcn, hc, hcp⟩ := exists_isGeodesicChain_through
      B.symmetricGenerating hp
    let n : ℕ := wordDist B.carrier x y
    have hcqg : Hyperbolic.IsQuasiGeodesic A.carrier K 0 n c := by
      intro i hi j hj hij
      have hcij : wordDist B.carrier (c i) (c j) = j - i := hc i j hij hj
      constructor
      · simpa [hcij] using hA_le (c i) (c j)
      · have h := hB_le (c i) (c j)
        rw [hcij] at h
        simpa using h
    obtain ⟨q, hq, hpq⟩ := hMorse n c hcqg (wordDist B.carrier x p) (by
      have hp' : wordDist B.carrier x p + wordDist B.carrier p y = n := hp
      omega)
    rw [hc0, hcn] at hq
    rw [hcp] at hpq
    rcases hslim x y z q hq with ⟨r, hr, hqr⟩ | ⟨r, hr, hqr⟩
    · obtain ⟨s, hs, hrs⟩ := exists_target_between_near_source_between
        A.symmetricGenerating B.symmetricGenerating hK hB_le hA_le hfour hMorse hr
      refine Or.inl ⟨s, hs, ?_⟩
      have hpqB := hB_le p q
      have hqrB := hB_le q r
      have hpqB' : wordDist B.carrier p q ≤ K * R :=
        hpqB.trans (Nat.mul_le_mul_left K hpq)
      have hqrB' : wordDist B.carrier q r ≤ K * (4 * δ) :=
        hqrB.trans (Nat.mul_le_mul_left K hqr)
      have htri1 := wordDist_triangle B.symmetricGenerating p q r
      have htri2 := wordDist_triangle B.symmetricGenerating p r s
      dsimp [D]
      omega
    · obtain ⟨s, hs, hrs⟩ := exists_target_between_near_source_between
        A.symmetricGenerating B.symmetricGenerating hK hB_le hA_le hfour hMorse hr
      refine Or.inr ⟨s, hs, ?_⟩
      have hpqB := hB_le p q
      have hqrB := hB_le q r
      have hpqB' : wordDist B.carrier p q ≤ K * R :=
        hpqB.trans (Nat.mul_le_mul_left K hpq)
      have hqrB' : wordDist B.carrier q r ≤ K * (4 * δ) :=
        hqrB.trans (Nat.mul_le_mul_left K hqr)
      have htri1 := wordDist_triangle B.symmetricGenerating p q r
      have htri2 := wordDist_triangle B.symmetricGenerating p r s
      dsimp [D]
      omega
  let δ' : ℕ := 3 * D + 1
  refine ⟨(δ' : ℝ), isHyperbolicSpace_cayley_of_fourPoint B ?_⟩
  exact Hyperbolic.isFourPointHyperbolic_of_isSlimTriangles B.symmetricGenerating hslimB

end FiniteChange

namespace RelGenSet

variable {G : Type u} [Group G] {Λ : Type w}

/-- A finite one-way difference of relative bases gives a finite one-way
difference of the total relative alphabets, because the peripheral family is
unchanged. -/
theorem alphabet_diff_finite_of_base_diff (D D' : RelGenSet G Λ)
    (hfam : D'.fam = D.fam) (hfin : (D.base \ D'.base).Finite) :
    (D.alphabet.carrier \ D'.alphabet.carrier).Finite := by
  refine hfin.subset ?_
  rintro x ⟨hx, hxnot⟩
  refine ⟨?_, ?_⟩
  · rcases hx with hx | hx
    · exact hx
    · exfalso
      apply hxnot
      exact Or.inr (by rwa [hfam])
  · intro hx'
    exact hxnot (Or.inl hx')

/-- The hyperbolicity clause of hyperbolic embeddedness crosses a finite
symmetric difference of relative bases. -/
theorem exists_hyperbolic_of_finite_symmDiff (D D' : RelGenSet G Λ)
    (hfam : D'.fam = D.fam)
    (hdiff : ((D.base \ D'.base) ∪ (D'.base \ D.base)).Finite)
    (hD : ∃ d : ℝ, IsHyperbolicSpace d (Cayley D.alphabet)) :
    ∃ d' : ℝ, IsHyperbolicSpace d' (Cayley D'.alphabet) := by
  have hbase12 : (D.base \ D'.base).Finite := hdiff.subset Set.subset_union_left
  have hbase21 : (D'.base \ D.base).Finite := hdiff.subset Set.subset_union_right
  have halph12 := alphabet_diff_finite_of_base_diff D D' hfam hbase12
  have halph21 := alphabet_diff_finite_of_base_diff D' D hfam.symm hbase21
  obtain ⟨K, hK, hcomp⟩ := FiniteChange.exists_bilipschitz_of_finite_diff
    D.alphabet.symmetricGenerating D'.alphabet.symmetricGenerating halph12 halph21
  obtain ⟨d, hd⟩ := hD
  exact FiniteChange.exists_hyperbolic_of_bilipschitz D.alphabet D'.alphabet hK
    (fun x y => (hcomp x y).1) (fun x y => (hcomp x y).2) hd

/-- **Dahmani--Guirardel--Osin, Corollary 4.27.** -/
theorem dgoCorollary427 : DGOCorollary427.{u, w} := by
  intro G _ Λ D D' hfam hdiff
  have hloc := localFiniteness_iff_of_finite_symmDiff D D' hfam.symm hdiff
  constructor
  · intro hD
    exact ⟨exists_hyperbolic_of_finite_symmDiff D D' hfam.symm hdiff hD.hyperbolic,
      hloc.mp hD.locallyFinite⟩
  · intro hD'
    have hdiff' : ((D'.base \ D.base) ∪ (D.base \ D'.base)).Finite :=
      (hdiff.subset Set.subset_union_right).union
        (hdiff.subset Set.subset_union_left)
    exact ⟨exists_hyperbolic_of_finite_symmDiff D' D hfam hdiff' hD'.hyperbolic,
      hloc.mpr hD'.locallyFinite⟩

end RelGenSet

end GGT
end GroupApproximation
