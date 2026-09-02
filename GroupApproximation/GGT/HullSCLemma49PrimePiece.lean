import GroupApproximation.GGT.HullSCLemma49ShadowIndices

/-!
# The prime-piece contradiction in Hull's Lemma 4.9

This module proves the non-Greendlinger part of Case 1 in Osin's Lemma 6.3,
which Hull invokes in the proof of Lemma 4.9.  Two equal separated blocks on
the geodesic power boundary give two disjoint subwords of the selected relator.
The four shadow connectors express the value of the second subword as the
value, or inverse value, of the first subword with two short multipliers.

The selected Greendlinger cell is used at `mu = 1/1000`.  The final
small-cancellation input is used at `mu = 1/100000`; parameter monotonicity
allows the latter input to supply the former certificate.  The explicit
constant leaves room for the two quasi-geodesic losses and the four shadow
connectors.  The conclusion is `False`, obtained from the already proved
prime-piece estimate in `HullSCLemma49Correction`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

/-! ## List intervals and cyclic rotation -/

/-- The half-open interval `[i,j)` of a list. -/
def listInterval {Alpha : Type*} (word : List Alpha) (i j : ℕ) : List Alpha :=
  (word.drop i).take (j - i)

/-- An interval ending inside a word has its parameter length. -/
theorem length_listInterval {Alpha : Type*} (word : List Alpha)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ word.length) :
    (listInterval word i j).length = j - i := by
  simp only [listInterval, List.length_take, List.length_drop]
  omega

/-- Rotating at the first of four ordered indices makes the first two
designated intervals into disjoint subwords in linear order. -/
theorem rotate_eq_four_listIntervals {Alpha : Type*} (word : List Alpha)
    {a b c d : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hd : d ≤ word.length) :
    word.rotate a =
      listInterval word a b ++ listInterval word b c ++
        listInterval word c d ++ (word.drop d ++ word.take a) := by
  have ha : a ≤ word.length := le_trans hab (le_trans hbc (le_trans hcd hd))
  have habDrop : listInterval word a b ++ word.drop b = word.drop a := by
    have h := List.drop_take_append_drop word a (b - a)
    rw [Nat.add_sub_of_le hab] at h
    exact h
  have hbcDrop : listInterval word b c ++ word.drop c = word.drop b := by
    have h := List.drop_take_append_drop word b (c - b)
    rw [Nat.add_sub_of_le hbc] at h
    exact h
  have hcdDrop : listInterval word c d ++ word.drop d = word.drop c := by
    have h := List.drop_take_append_drop word c (d - c)
    rw [Nat.add_sub_of_le hcd] at h
    exact h
  rw [List.rotate_eq_drop_append_take ha, ← habDrop, ← hbcDrop,
    ← hcdDrop]
  simp only [List.append_assoc]

/-! ## Repeated-block endpoint values -/

/-- The first two power-arc endpoints span the first repeated block. -/
theorem Lemma49RepeatedBoundaryBlocks.first_powerArc_span
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z)
    (B : Lemma49RepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc) :
    (C.powerArcVertex 0)⁻¹ * C.powerArcVertex B.block.length =
      GGT.RelLetter.listVal B.block := by
  have htake : C.boundaryArc.take B.block.length = B.block := by
    calc
      C.boundaryArc.take B.block.length =
          (B.block ++ B.middle ++ B.block ++ B.tail).take B.block.length :=
        congrArg (List.take B.block.length) B.decomposition
      _ = B.block := by
        simpa only [List.append_assoc] using
          (List.take_left :
            (B.block ++ (B.middle ++ B.block ++ B.tail)).take
                B.block.length = B.block)
  simp only [Lemma49RelativeGreendlingerCell.powerArcVertex, List.take_zero,
    GGT.RelLetter.listVal_nil, mul_one, htake]
  group

/-- The later two power-arc endpoints span the second copy of the same block. -/
theorem Lemma49RepeatedBoundaryBlocks.second_powerArc_span
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z)
    (B : Lemma49RepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc) :
    (C.powerArcVertex (B.block.length + B.middle.length))⁻¹ *
        C.powerArcVertex
          (B.block.length + B.middle.length + B.block.length) =
      GGT.RelLetter.listVal B.block := by
  have htake₂ : C.boundaryArc.take (B.block.length + B.middle.length) =
      B.block ++ B.middle := by
    calc
      C.boundaryArc.take (B.block.length + B.middle.length) =
          (B.block ++ B.middle ++ B.block ++ B.tail).take
            (B.block.length + B.middle.length) :=
        congrArg (List.take (B.block.length + B.middle.length))
          B.decomposition
      _ = B.block ++ B.middle := by
        simpa only [List.length_append, List.append_assoc] using
          (List.take_left :
            ((B.block ++ B.middle) ++ (B.block ++ B.tail)).take
                (B.block ++ B.middle).length = B.block ++ B.middle)
  have htake₃ : C.boundaryArc.take
      (B.block.length + B.middle.length + B.block.length) =
      B.block ++ B.middle ++ B.block := by
    calc
      C.boundaryArc.take
          (B.block.length + B.middle.length + B.block.length) =
          (B.block ++ B.middle ++ B.block ++ B.tail).take
            (B.block.length + B.middle.length + B.block.length) :=
        congrArg
          (List.take (B.block.length + B.middle.length + B.block.length))
          B.decomposition
      _ = B.block ++ B.middle ++ B.block := by
        simpa only [List.length_append] using
          (List.take_left :
            ((B.block ++ B.middle ++ B.block) ++ B.tail).take
                (B.block ++ B.middle ++ B.block).length =
              B.block ++ B.middle ++ B.block)
  simp only [Lemma49RelativeGreendlingerCell.powerArcVertex, htake₂, htake₃,
    RelWord.listVal_append]
  group

/-! ## Shadow defects and relator segment values -/

/-- The short group element from a power-arc endpoint to its shadow. -/
def Lemma49ContiguityShadow.defect
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z} {K : ℕ}
    (Sh : Lemma49ContiguityShadow C K) (i : ℕ) : G :=
  (C.powerArcVertex i)⁻¹ * C.exteriorVertex (Sh.index i)

/-- A shadow defect has norm at most the shadow constant. -/
theorem Lemma49ContiguityShadow.wordNorm_defect_le
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z} {K : ℕ}
    (Sh : Lemma49ContiguityShadow C K) {i : ℕ}
    (hi : i ≤ C.boundaryArc.length) :
    wordNorm D.alphabet.carrier (Sh.defect i) ≤ K := by
  exact Sh.close i hi

/-- A product of an inverse defect and a defect has norm at most `2*K`. -/
theorem Lemma49ContiguityShadow.wordNorm_defect_inv_mul_defect_le
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z} {K : ℕ}
    (Sh : Lemma49ContiguityShadow C K) {i j : ℕ}
    (hi : i ≤ C.boundaryArc.length) (hj : j ≤ C.boundaryArc.length) :
    wordNorm D.alphabet.carrier ((Sh.defect i)⁻¹ * Sh.defect j) ≤ 2 * K := by
  have hiNorm := Sh.wordNorm_defect_le hi
  have hjNorm := Sh.wordNorm_defect_le hj
  have hiInv : wordNorm D.alphabet.carrier (Sh.defect i)⁻¹ ≤ K := by
    rw [wordNorm_inv D.alphabet.symmetricGenerating]
    exact hiNorm
  have hmul := wordNorm_mul_le D.alphabet.symmetricGenerating
    (Sh.defect i)⁻¹ (Sh.defect j)
  omega

/-- A relator interval inside the exposed prefix spells the difference of its
two exterior vertices. -/
theorem Lemma49RelativeGreendlingerCell.listVal_relatorInterval
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ C.contiguity.exterior.length) :
    GGT.RelLetter.listVal (listInterval C.relator i j) =
      (C.exteriorVertex i)⁻¹ * C.exteriorVertex j := by
  have hi : i ≤ C.contiguity.exterior.length := le_trans hij hj
  have hiTake : C.relator.take i = C.contiguity.exterior.take i := by
    calc
      C.relator.take i =
          (C.contiguity.exterior ++ C.contiguity.remainder).take i :=
        congrArg (List.take i) C.contiguity.relator_decomposition
      _ = C.contiguity.exterior.take i := by
        rw [List.take_append_of_le_length hi]
  have hjTake : C.relator.take j = C.contiguity.exterior.take j := by
    calc
      C.relator.take j =
          (C.contiguity.exterior ++ C.contiguity.remainder).take j :=
        congrArg (List.take j) C.contiguity.relator_decomposition
      _ = C.contiguity.exterior.take j := by
        rw [List.take_append_of_le_length hj]
  have hspan := GGT.OsinComponents.listVal_segment C.relator 1 hij
  rw [
    GGT.OsinComponents.vertex_eq_mul_listVal_take,
    GGT.OsinComponents.vertex_eq_mul_listVal_take, one_mul, one_mul,
    hiTake, hjTake] at hspan
  change GGT.RelLetter.listVal
      ((C.relator.drop i).take (j - i)) =
    (GGT.RelLetter.listVal (C.contiguity.exterior.take i))⁻¹ *
      GGT.RelLetter.listVal (C.contiguity.exterior.take j)
  rw [← hspan]
  group

/-! ## Quantitative size of a shadow interval -/

/-- The parameter span of two distinct shadows is bounded below by the
quasi-geodesic progress of the corresponding power interval. -/
theorem Lemma49ContiguityShadow.indexSpan_lower
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps mu Z} {K b : ℕ}
    (Sh : Lemma49ContiguityShadow C K)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b
      C.powerArcVertex C.boundaryArc.length)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ C.boundaryArc.length) :
    ((y - x : ℕ) : ℝ) / 4 - b - 2 * K ≤
      (max (Sh.index x) (Sh.index y) - min (Sh.index x) (Sh.index y) : ℕ) := by
  have hx : x ≤ C.boundaryArc.length := le_trans hxy hy
  have hcloseX := Sh.close x hx
  have hcloseY := Sh.close y hy
  have hspanDist : wordDist D.alphabet.carrier
      (C.exteriorVertex (Sh.index x)) (C.exteriorVertex (Sh.index y)) ≤
      max (Sh.index x) (Sh.index y) - min (Sh.index x) (Sh.index y) := by
    rcases le_total (Sh.index x) (Sh.index y) with hforward | hreverse
    · simpa [Nat.max_eq_right hforward, Nat.min_eq_left hforward] using
        (hRel (Sh.index x) (Sh.index y) hforward (Sh.index_le y hy)).2
    · have hraw :=
        (hRel (Sh.index y) (Sh.index x) hreverse (Sh.index_le x hx)).2
      rw [wordDist_comm D.alphabet.symmetricGenerating] at hraw
      simpa [Nat.max_eq_left hreverse, Nat.min_eq_right hreverse] using hraw
  have hcloseY' : wordDist D.alphabet.carrier
      (C.exteriorVertex (Sh.index y)) (C.powerArcVertex y) ≤ K := by
    rw [wordDist_comm D.alphabet.symmetricGenerating]
    exact hcloseY
  have htri₁ := wordDist_triangle D.alphabet.symmetricGenerating
    (C.powerArcVertex x) (C.exteriorVertex (Sh.index x))
      (C.exteriorVertex (Sh.index y))
  have htri₂ := wordDist_triangle D.alphabet.symmetricGenerating
    (C.powerArcVertex x) (C.exteriorVertex (Sh.index y))
      (C.powerArcVertex y)
  have hdistUpper : wordDist D.alphabet.carrier
      (C.powerArcVertex x) (C.powerArcVertex y) ≤
      2 * K +
        (max (Sh.index x) (Sh.index y) - min (Sh.index x) (Sh.index y)) := by
    omega
  have hdistUpperReal :
      (wordDist D.alphabet.carrier
        (C.powerArcVertex x) (C.powerArcVertex y) : ℝ) ≤
        2 * (K : ℝ) +
          (max (Sh.index x) (Sh.index y) - min (Sh.index x) (Sh.index y) : ℕ) := by
    exact_mod_cast hdistUpper
  have hpowLower := (hPow x y hxy hy).1
  linarith [hdistUpperReal]

/-- Every shadow interval corresponding to one repeated block is longer than
`1/100000` of the selected relator. -/
theorem Lemma49ContiguityShadow.repeatedBlock_indexSpan_large
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho b K : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z}
    (Sh : Lemma49ContiguityShadow C K)
    (B : Lemma49RepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b
      C.powerArcVertex C.boundaryArc.length)
    (hscale : 1000 * (4 * b + 24 * K + 18 * eps + 18) ≤ rho)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ C.boundaryArc.length)
    (hgap : y - x = B.block.length) :
    (1 / 100000 : ℝ) * (C.relator.length : ℝ) ≤
      (max (Sh.index x) (Sh.index y) - min (Sh.index x) (Sh.index y) : ℕ) := by
  have hspan := Sh.indexSpan_lower hRel hPow hxy hy
  have hrho := hinput.long C.relator C.relator_mem
  have hrelatorScaleNat :
      1000 * (4 * b + 24 * K + 18 * eps + 18) ≤ C.relator.length :=
    le_trans hscale hrho
  have hrelatorScale :
      (1000 : ℝ) *
          (4 * (b : ℝ) + 24 * (K : ℝ) + 18 * (eps : ℝ) + 18) ≤
        (C.relator.length : ℝ) := by
    exact_mod_cast hrelatorScaleNat
  have hexterior := C.exterior_large
  have harc := C.boundaryArc_lower hinput
  have hdivisionNat : C.boundaryArc.length <
      100 * (C.boundaryArc.length / 100 + 1) := by
    have hmod : C.boundaryArc.length % 100 < 100 := by omega
    have hdecomp := Nat.div_add_mod C.boundaryArc.length 100
    omega
  have hdivision : (C.boundaryArc.length : ℝ) <
      100 * ((C.boundaryArc.length / 100 : ℕ) + 1) := by
    exact_mod_cast hdivisionNat
  rw [hgap, B.block_length] at hspan
  norm_num at hexterior hspan ⊢
  linarith

/-! ## The prime-piece contradiction -/

/-- The long-arc shadow data contradicts the prime-piece clause of Hull's
`C₁` condition.  This is Case 1 of Osin Lemma 6.3 after the single shared
Greendlinger certificate has selected the cell. -/
theorem false_of_lemma49LongArc_contiguityShadow
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps epsFinal rho b K : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (B : Lemma49RepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc)
    (Sh : Lemma49ContiguityShadow C K)
    (hcertificateInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hfinalInput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      epsFinal (1 / 100000) rho)
    (hRel : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1
      C.exteriorVertex C.contiguity.exterior.length)
    (hPow : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b
      C.powerArcVertex C.boundaryArc.length)
    (hscale : 1000 * (4 * b + 24 * K + 18 * eps + 18) ≤ rho)
    (hconnectors : 2 * K ≤ epsFinal) : False := by
  let p₀ := 0
  let p₁ := B.block.length
  let p₂ := B.block.length + B.middle.length
  let p₃ := B.block.length + B.middle.length + B.block.length
  have hp₀₁ : p₀ ≤ p₁ := by dsimp [p₀, p₁]; omega
  have hp₁₂ : p₁ ≤ p₂ := by dsimp [p₁, p₂]; omega
  have hp₁₃ : p₁ ≤ p₃ := by dsimp [p₁, p₃]; omega
  have hp₂₃ : p₂ ≤ p₃ := by dsimp [p₂, p₃]; omega
  have hp₁ : p₁ ≤ C.boundaryArc.length := by
    exact B.firstEnd_le
  have hp₂ : p₂ ≤ C.boundaryArc.length := by
    exact B.secondStart_le
  have hp₃ : p₃ ≤ C.boundaryArc.length := by
    exact B.secondEnd_le
  have hp₀ : p₀ ≤ C.boundaryArc.length := by
    exact Nat.zero_le _
  have harcScale := C.boundaryArc_shadow_scale hcertificateInput hscale
  have hblockFar := B.block_shadow_far harcScale
  have hmiddleFar := B.middle_shadow_far harcScale
  have hj₀₁ : Sh.index p₀ < Sh.index p₁ := by
    apply Sh.index_strictMono_of_far hRel hPow hp₀₁ hp₁
    dsimp [p₀, p₁]
    exact hblockFar
  have hj₁₂ : Sh.index p₁ < Sh.index p₂ := by
    apply Sh.index_strictMono_of_far hRel hPow hp₁₂ hp₂
    dsimp [p₁, p₂]
    rw [Nat.add_sub_cancel_left]
    exact hmiddleFar
  have hj₁₃ : Sh.index p₁ < Sh.index p₃ := by
    apply Sh.index_strictMono_of_far hRel hPow hp₁₃ hp₃
    dsimp [p₁, p₃]
    omega
  have hj₂₃ne : Sh.index p₂ ≠ Sh.index p₃ := by
    apply Sh.index_ne_of_far hPow hp₂₃ hp₃
    dsimp [p₂, p₃]
    omega
  let j₀ := Sh.index p₀
  let j₁ := Sh.index p₁
  let j₂ := Sh.index p₂
  let j₃ := Sh.index p₃
  let c := min j₂ j₃
  let d := max j₂ j₃
  have hj₀₁' : j₀ < j₁ := hj₀₁
  have hj₁c : j₁ < c := by
    dsimp [c, j₁, j₂, j₃]
    rw [lt_min_iff]
    exact ⟨hj₁₂, hj₁₃⟩
  have hcd : c < d := by
    dsimp [c, d, j₂, j₃]
    exact min_lt_max.mpr hj₂₃ne
  have hdExterior : d ≤ C.contiguity.exterior.length := by
    dsimp [d, j₂, j₃]
    rw [max_le_iff]
    exact ⟨Sh.index_le p₂ hp₂, Sh.index_le p₃ hp₃⟩
  have hdRelator : d ≤ C.relator.length :=
    le_trans hdExterior C.contiguity.exterior_length_le_relator
  let first := listInterval C.relator j₀ j₁
  let middle := listInterval C.relator j₁ c
  let second := listInterval C.relator c d
  let tail := C.relator.drop d ++ C.relator.take j₀
  let rotated := C.relator.rotate j₀
  have hsplit : rotated = first ++ middle ++ second ++ tail := by
    exact rotate_eq_four_listIntervals C.relator hj₀₁'.le hj₁c.le
      hcd.le hdRelator
  have hrotatedMem : rotated ∈ RelWord.symmetrized v := by
    exact hfinalInput.rotate_mem C.relator C.relator_mem j₀
  have hfirstLength : first.length = j₁ - j₀ := by
    exact length_listInterval C.relator hj₀₁'.le
      (le_trans hj₁c.le (le_trans hcd.le hdRelator))
  have hsecondLength : second.length = d - c := by
    exact length_listInterval C.relator hcd.le hdRelator
  have hfirstLargeRaw := Sh.repeatedBlock_indexSpan_large B hcertificateInput
    hRel hPow hscale hp₀₁ hp₁ (by dsimp [p₀, p₁])
  have hfirstLarge : (1 / 100000 : ℝ) * (rotated.length : ℝ) ≤
      (first.length : ℝ) := by
    rw [List.length_rotate, hfirstLength]
    dsimp [j₀, j₁]
    exact hfirstLargeRaw
  have hsecondLargeRaw := Sh.repeatedBlock_indexSpan_large B hcertificateInput
    hRel hPow hscale hp₂₃ hp₃ (by dsimp [p₂, p₃])
  have hsecondLarge : (1 / 100000 : ℝ) * (rotated.length : ℝ) ≤
      (second.length : ℝ) := by
    rw [List.length_rotate, hsecondLength]
    dsimp [c, d, j₂, j₃]
    exact hsecondLargeRaw
  let e₀ := Sh.defect p₀
  let e₁ := Sh.defect p₁
  let e₂ := Sh.defect p₂
  let e₃ := Sh.defect p₃
  have he₀ : C.exteriorVertex j₀ = C.powerArcVertex p₀ * e₀ := by
    dsimp [e₀, j₀, Lemma49ContiguityShadow.defect]
    group
  have he₁ : C.exteriorVertex j₁ = C.powerArcVertex p₁ * e₁ := by
    dsimp [e₁, j₁, Lemma49ContiguityShadow.defect]
    group
  have he₂ : C.exteriorVertex j₂ = C.powerArcVertex p₂ * e₂ := by
    dsimp [e₂, j₂, Lemma49ContiguityShadow.defect]
    group
  have he₃ : C.exteriorVertex j₃ = C.powerArcVertex p₃ * e₃ := by
    dsimp [e₃, j₃, Lemma49ContiguityShadow.defect]
    group
  have hpower₀₁ := B.first_powerArc_span C
  have hpower₂₃ := B.second_powerArc_span C
  have hfirstValue : GGT.RelLetter.listVal first =
      e₀⁻¹ * GGT.RelLetter.listVal B.block * e₁ := by
    dsimp [first]
    rw [C.listVal_relatorInterval hj₀₁'.le
      (le_trans hj₁c.le (le_trans hcd.le hdExterior)), he₀, he₁]
    rw [← hpower₀₁]
    group
  by_cases hforward : j₂ ≤ j₃
  · have hcEq : c = j₂ := by exact Nat.min_eq_left hforward
    have hdEq : d = j₃ := by exact Nat.max_eq_right hforward
    have hsecondValue : GGT.RelLetter.listVal second =
        e₂⁻¹ * GGT.RelLetter.listVal B.block * e₃ := by
      dsimp [second]
      rw [hcEq, hdEq]
      rw [C.listVal_relatorInterval hforward
        (by simpa [j₃] using Sh.index_le p₃ hp₃)]
      rw [he₂, he₃, ← hpower₂₃]
      group
    let left := e₂⁻¹ * e₀
    let right := e₁⁻¹ * e₃
    have hleft : wordNorm D.alphabet.carrier left ≤ epsFinal := by
      exact le_trans (Sh.wordNorm_defect_inv_mul_defect_le hp₂ hp₀)
        hconnectors
    have hright : wordNorm D.alphabet.carrier right ≤ epsFinal := by
      exact le_trans (Sh.wordNorm_defect_inv_mul_defect_le hp₁ hp₃)
        hconnectors
    apply false_of_two_large_close_relator_subwords hfinalInput hrotatedMem
      hsplit hleft hright
    · left
      rw [hsecondValue, hfirstValue]
      group
    · exact hfirstLarge
    · exact hsecondLarge
  · have hreverse : j₃ ≤ j₂ := by omega
    have hcEq : c = j₃ := by exact Nat.min_eq_right hreverse
    have hdEq : d = j₂ := by exact Nat.max_eq_left hreverse
    have hsecondValue : GGT.RelLetter.listVal second =
        e₃⁻¹ * (GGT.RelLetter.listVal B.block)⁻¹ * e₂ := by
      dsimp [second]
      rw [hcEq, hdEq]
      rw [C.listVal_relatorInterval hreverse
        (by simpa [j₂] using Sh.index_le p₂ hp₂)]
      rw [he₃, he₂, ← hpower₂₃]
      group
    let left := e₃⁻¹ * e₁
    let right := e₀⁻¹ * e₂
    have hleft : wordNorm D.alphabet.carrier left ≤ epsFinal := by
      exact le_trans (Sh.wordNorm_defect_inv_mul_defect_le hp₃ hp₁)
        hconnectors
    have hright : wordNorm D.alphabet.carrier right ≤ epsFinal := by
      exact le_trans (Sh.wordNorm_defect_inv_mul_defect_le hp₀ hp₂)
        hconnectors
    apply false_of_two_large_close_relator_subwords hfinalInput hrotatedMem
      hsplit hleft hright
    · right
      rw [hsecondValue, hfirstValue]
      group
    · exact hfirstLarge
    · exact hsecondLarge

/-! ## Model check -/

/-- Four ordered indices produce the expected cyclic interval decomposition
on a concrete list. -/
theorem rotate_four_listIntervals_model :
    ([0, 1, 2, 3, 4, 5] : List ℕ).rotate 1 =
      listInterval [0, 1, 2, 3, 4, 5] 1 2 ++
      listInterval [0, 1, 2, 3, 4, 5] 2 4 ++
      listInterval [0, 1, 2, 3, 4, 5] 4 5 ++
      (([0, 1, 2, 3, 4, 5] : List ℕ).drop 5 ++
        ([0, 1, 2, 3, 4, 5] : List ℕ).take 1) := by
  norm_num [listInterval]

end HullSC
end GroupApproximation
