import GroupApproximation.GGT.HullSCLemma49FromRelativeGreendlinger

/-!
# The periodic long arc in Hull's Lemma 4.9

This module proves the finite-word part of the long-arc case in the proof of
Hull's Lemma 4.9.  A factor of a positive power inherits the period of the
base word.  When the factor has length at least four thirds of that period,
two equal blocks, each one hundredth of the factor, can be placed inside it
with at least one quarter of the factor between them.

The placement is deliberately explicit.  If `b = |arc| / 100`, the second
copy starts at the first multiple of the period at or beyond
`b + |arc| / 4`.  Periodicity makes the two blocks equal.  The inequality
`4 * period <= 3 * |arc|` leaves enough room after that multiple for the
second block.  The resulting four-list decomposition is exactly the
`W V₁ W V₂` decomposition used in Osin's proof of Lemma 6.3.

No geometric statement is introduced here.  In particular the output below
is a structure containing lists and equalities, not a new proposition that a
later theorem would have to assume.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

/-! ## Equal blocks at a multiple of a period -/

/-- Two blocks of the same length, whose starting positions differ by a
multiple of a period, are equal whenever both blocks fit in the word. -/
theorem take_eq_drop_take_of_hasPeriod_of_dvd
    {Alpha : Type u} {word : List Alpha} {period offset blockLength : ℕ}
    (hperiod : List.HasPeriod word period)
    (hoffset : period ∣ offset)
    (hfit : offset + blockLength ≤ word.length) :
    word.take blockLength = (word.drop offset).take blockLength := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < blockLength
  · have hiWord : i < word.length := by omega
    have hshiftWord : offset + i < word.length := by omega
    have hbase :=
      List.hasPeriod_iff_forall_getElem?_mod.mp hperiod i hiWord
    have hshift :=
      List.hasPeriod_iff_forall_getElem?_mod.mp hperiod (offset + i) hshiftWord
    obtain ⟨q, hq⟩ := hoffset
    have hmod : (offset + i) % period = i % period := by
      rw [hq, Nat.add_mod, Nat.mul_mod]
      simp
    rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
      List.getElem?_drop, hshift, hmod, ← hbase]
  · have hiblock : blockLength ≤ i := by omega
    have hleft : (word.take blockLength)[i]? = none := by
      apply List.getElem?_eq_none
      simp only [List.length_take]
      omega
    have hright : ((word.drop offset).take blockLength)[i]? = none := by
      apply List.getElem?_eq_none
      simp only [List.length_take]
      omega
    rw [hleft, hright]

/-! ## The arithmetic placement -/

/-- The first period multiple at or beyond `blockLength + total / 4` fits,
with another `blockLength` letters after it, provided the period occupies at
most three quarters of the total and `blockLength = total / 100`.

The four conclusions say, respectively: the chosen offset is a period
multiple; the first block ends before it; the gap is at least a quarter of the
total; and the second block fits. -/
theorem exists_periodic_block_offset
    {period total : ℕ} (hperiodPos : 0 < period)
    (hlong : 4 * period ≤ 3 * total) :
    ∃ offset : ℕ,
      period ∣ offset ∧
      total / 100 ≤ offset ∧
      total / 4 ≤ offset - total / 100 ∧
      offset + total / 100 ≤ total := by
  let blockLength := total / 100
  let lower := blockLength + total / 4
  have hblockBudget : 100 * blockLength ≤ total := by
    dsimp [blockLength]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self total 100
  have hquarterBudget : 4 * (total / 4) ≤ total :=
    by simpa [Nat.mul_comm] using Nat.div_mul_le_self total 4
  by_cases hlower : lower ≤ period
  · refine ⟨period, dvd_rfl, ?_, ?_, ?_⟩
    · dsimp [lower] at hlower
      omega
    · dsimp [lower] at hlower
      omega
    · omega
  · have hperiodLower : period < lower := by omega
    let quotient := lower / period
    let offset := (quotient + 1) * period
    have hmod : lower % period < period := Nat.mod_lt _ hperiodPos
    have hdivision : period * quotient + lower % period = lower := by
      simpa [quotient] using Nat.div_add_mod lower period
    have hoffsetForm : offset = period * quotient + period := by
      simp only [offset, Nat.add_mul, one_mul, Nat.mul_comm]
    have hlowerOffset : lower ≤ offset := by omega
    have hoffsetUpper : offset ≤ lower + period := by omega
    have htwoLower : offset ≤ 2 * lower := by omega
    have hroom : 2 * lower + blockLength ≤ total := by
      dsimp [lower]
      omega
    refine ⟨offset, ?_, ?_, ?_, ?_⟩
    · exact ⟨quotient + 1, by simp [offset, Nat.mul_comm]⟩
    · dsimp [lower] at hlowerOffset
      omega
    · dsimp [lower] at hlowerOffset
      omega
    · omega

/-! ## Literal `W V₁ W V₂` data -/

/-- The explicit repeated-block decomposition of a long periodic arc. -/
structure Lemma49RepeatedBoundaryBlocks (Alpha : Type u) (arc : List Alpha) where
  /-- The repeated word `W`. -/
  block : List Alpha
  /-- The intervening word `V₁`. -/
  middle : List Alpha
  /-- The final word `V₂`. -/
  tail : List Alpha
  /-- The literal decomposition from Case 1 of Osin's Lemma 6.3. -/
  decomposition : arc = block ++ middle ++ block ++ tail
  /-- Each repeated block occupies one hundredth of the selected arc. -/
  block_length : block.length = arc.length / 100
  /-- The two occurrences are separated by at least a quarter of the arc. -/
  middle_long : arc.length / 4 ≤ middle.length

/-- A long periodic word has the preceding literal repeated-block
decomposition. -/
theorem exists_repeatedBoundaryBlocks_of_hasPeriod
    {Alpha : Type u} {arc : List Alpha} {period : ℕ}
    (hperiodPos : 0 < period)
    (hperiod : List.HasPeriod arc period)
    (hlong : 4 * period ≤ 3 * arc.length) :
    Nonempty (Lemma49RepeatedBoundaryBlocks Alpha arc) := by
  obtain ⟨offset, hoffsetPeriod, hblockOffset, hgap, hfit⟩ :=
    exists_periodic_block_offset hperiodPos hlong
  let blockLength := arc.length / 100
  let block := arc.take blockLength
  let middle := (arc.drop blockLength).take (offset - blockLength)
  let second := (arc.drop offset).take blockLength
  let tail := arc.drop (offset + blockLength)
  have hblockLength : block.length = blockLength := by
    dsimp [block]
    rw [List.length_take]
    omega
  have hmiddleLength : middle.length = offset - blockLength := by
    dsimp [middle]
    rw [List.length_take, List.length_drop]
    omega
  have hsecond : second = block := by
    dsimp [second, block]
    exact (take_eq_drop_take_of_hasPeriod_of_dvd hperiod
      hoffsetPeriod hfit).symm
  have htakeOffset : arc.take offset = block ++ middle := by
    dsimp [block, middle]
    rw [← List.take_add]
    congr 1
    omega
  have htakeSecond : arc.take (offset + blockLength) =
      arc.take offset ++ second := by
    dsimp [second]
    rw [← List.take_add]
  have hdecomposition : arc = block ++ middle ++ block ++ tail := by
    calc
      arc = arc.take (offset + blockLength) ++
          arc.drop (offset + blockLength) :=
        (List.take_append_drop (offset + blockLength) arc).symm
      _ = (arc.take offset ++ second) ++ tail := by
        rw [htakeSecond]
      _ = (block ++ middle ++ block) ++ tail := by
        rw [htakeOffset, hsecond]
      _ = block ++ middle ++ block ++ tail := by
        simp only [List.append_assoc]
  exact ⟨{
    block := block
    middle := middle
    tail := tail
    decomposition := hdecomposition
    block_length := by simpa [blockLength] using hblockLength
    middle_long := by rw [hmiddleLength]; exact hgap }⟩

/-! ## Application to a selected power-boundary arc -/

/-- The long arc selected from a positive geodesic power inherits the period
of the boundary word and therefore has two separated equal blocks. -/
theorem exists_repeatedBoundaryBlocks_of_lemma49PowerArc
    {Alpha : Type u} {word arc : List Alpha} {n : ℕ}
    (hn : 0 < n)
    (harc : arc <:+: lemma49BoundaryPower word n)
    (hperiodPos : 0 < word.length)
    (hlong : 4 * word.length ≤ 3 * arc.length) :
    Nonempty (Lemma49RepeatedBoundaryBlocks Alpha arc) := by
  have hperiodPower := hasPeriod_lemma49BoundaryPower word hn
  have hperiodArc : List.HasPeriod arc word.length :=
    hperiodPower.infix harc
  exact exists_repeatedBoundaryBlocks_of_hasPeriod hperiodPos hperiodArc hlong

/-! ## Every sub-period segment is geodesic -/

/-- A segment of the power boundary no longer than one period has full word
norm.  Periodicity rotates it into one copy of the boundary word, while
quotient-conjugacy minimality makes every cyclic rotation geodesic. -/
theorem wordNorm_listVal_powerSegment_eq_length
    {G : Type u} [Group G] {Lambda : Type*}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {n start segmentLength : ℕ} (hn : 0 < n) (hwordNe : word ≠ [])
    (hfit : start + segmentLength ≤
      (lemma49BoundaryPower word n).length)
    (hshortSegment : segmentLength ≤ word.length) :
    wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal
          ((lemma49BoundaryPower word n).drop start).take segmentLength) =
      segmentLength := by
  let segment :=
    ((lemma49BoundaryPower word n).drop start).take segmentLength
  have hsegmentLength : segment.length = segmentLength := by
    dsimp [segment]
    rw [List.length_take, List.length_drop]
    omega
  have hsegmentInfix : segment <:+: lemma49BoundaryPower word n := by
    exact (List.take_prefix segmentLength
      ((lemma49BoundaryPower word n).drop start)).isInfix.trans
        (List.drop_suffix start (lemma49BoundaryPower word n)).isInfix
  obtain ⟨rotation, hrotation, hprefix⟩ :=
    exists_prefix_rotate_of_infix_lemma49BoundaryPower hn hwordNe
      hsegmentInfix (by rw [hsegmentLength]; exact hshortSegment)
  have hrotateLength : (word.rotate rotation).length = word.length :=
    List.length_rotate word rotation
  have hsegmentEq : segment = (word.rotate rotation).take segmentLength := by
    have htake := List.prefix_iff_eq_take.mp hprefix
    rw [hsegmentLength] at htake
    exact htake
  have hgeoRotate :=
    isGeodesicWord_rotate_of_shortestModuloConjugacy D N hshort hword
      hrotation.le
  have hgeoSegment := GGT.OsinComponents.isGeodesicWord_segment D hgeoRotate
    (i := 0) (j := segmentLength) (Nat.zero_le _) (by
      rw [hrotateLength]
      exact hshortSegment)
  have hend : GGT.OsinComponents.vertex 1 (word.rotate rotation)
      segmentLength = GGT.RelLetter.listVal segment := by
    rw [GGT.OsinComponents.vertex_eq_mul_listVal_take, one_mul,
      ← hsegmentEq]
  have hsegmentWord :
      ((word.rotate rotation).drop 0).take (segmentLength - 0) = segment := by
    rw [List.drop_zero, Nat.sub_zero, ← hsegmentEq]
  have hgeoSegment' : GGT.OsinComponents.IsGeodesicWord D 1
      (GGT.RelLetter.listVal segment) segment := by
    rw [GGT.OsinComponents.vertex_zero, hend, hsegmentWord] at hgeoSegment
    exact hgeoSegment
  have hlength := hgeoSegment'.2.2
  rw [wordDist_one_left, hsegmentLength] at hlength
  exact hlength.symm

/-- Equivalently, the vertices of a power boundary are their index distance
apart whenever that distance is at most one period. -/
theorem wordDist_powerVertices_eq_of_sub_le_period
    {G : Type u} [Group G] {Lambda : Type*}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {n i j : ℕ} (hn : 0 < n) (hwordNe : word ≠ [])
    (hij : i ≤ j) (hj : j ≤ (lemma49BoundaryPower word n).length)
    (hsub : j - i ≤ word.length) :
    wordDist D.alphabet.carrier
        (GGT.OsinComponents.vertex 1 (lemma49BoundaryPower word n) i)
        (GGT.OsinComponents.vertex 1 (lemma49BoundaryPower word n) j) =
      j - i := by
  have hfit : i + (j - i) ≤ (lemma49BoundaryPower word n).length := by
    omega
  have hnorm := wordNorm_listVal_powerSegment_eq_length D N hshort hword
    hn hwordNe hfit hsub
  have hvalue := GGT.OsinComponents.listVal_segment
    (lemma49BoundaryPower word n) 1 hij
  have hdiff :
      (GGT.OsinComponents.vertex 1 (lemma49BoundaryPower word n) i)⁻¹ *
          GGT.OsinComponents.vertex 1 (lemma49BoundaryPower word n) j =
        GGT.RelLetter.listVal
          ((lemma49BoundaryPower word n).drop i).take (j - i) := by
    rw [← hvalue]
    group
  show wordNorm D.alphabet.carrier
      ((GGT.OsinComponents.vertex 1 (lemma49BoundaryPower word n) i)⁻¹ *
        GGT.OsinComponents.vertex 1 (lemma49BoundaryPower word n) j) = j - i
  rw [hdiff]
  exact hnorm

/-! ## The repeated blocks clear the prime-piece cutoff -/

/-- At Hull's fixed `mu = 1/1000`, a sufficiently large relator threshold
makes each repeated block longer than `mu` times the selected relator.

This is the numerical end of equation (19) in Osin's proof.  The exterior
occupies at least `977/1000` of the relator, its `(4,1)` lower bound loses only
the two `eps`-connectors, and division by `100` loses fewer than one hundred
letters.  The deliberately generous scale below absorbs all three losses. -/
theorem Lemma49RepeatedBoundaryBlocks.large_relative_to_relator
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
    (B : Lemma49RepeatedBoundaryBlocks
      (GGT.RelLetter G Lambda) C.boundaryArc)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v)
      eps (1 / 1000) rho)
    (hscale : 1000 * (2 * eps + 100) ≤ rho) :
    (1 / 1000 : ℝ) * (C.relator.length : ℝ) ≤
      (B.block.length : ℝ) := by
  have hrelatorScaleNat :
      1000 * (2 * eps + 100) ≤ C.relator.length :=
    le_trans hscale (hinput.long C.relator C.relator_mem)
  have hrelatorScale :
      (1000 : ℝ) * (2 * (eps : ℝ) + 100) ≤
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
  have hblock : (B.block.length : ℝ) =
      (C.boundaryArc.length / 100 : ℕ) := by
    exact_mod_cast B.block_length
  norm_num at hexterior
  rw [hblock]
  linarith

/-! ## Model checks -/

/-- The concrete word `ababab` exhibits the non-vacuous repeated-block data
at period two.  The theorem is phrased at the arithmetic threshold used above,
so no special computation is hidden in the model. -/
theorem repeatedBoundaryBlocks_replicate_model
    {Alpha : Type u} (a : Alpha) :
    Nonempty (Lemma49RepeatedBoundaryBlocks Alpha (List.replicate 400 a)) := by
  have hperiod : List.HasPeriod (List.replicate 400 a) 1 := by
    rw [List.hasPeriod_iff_forall_getElem?_mod]
    intro i hi
    rw [List.getElem?_replicate_of_lt hi]
    have hmod : i % 1 < 400 := by omega
    rw [List.getElem?_replicate_of_lt hmod]
  apply exists_repeatedBoundaryBlocks_of_hasPeriod (period := 1) (by omega)
    hperiod
  rw [List.length_replicate]
  norm_num

end HullSC
end GroupApproximation
