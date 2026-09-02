import GroupApproximation.GGT.HullSCLemma44QuotientNormalForm

/-!
# Subwords of shortest quotient spellings

A shortest source spelling of a quotient element has the usual subword
property, with shortestness measured among all source words having the same
quotient value.  If a segment admitted a shorter quotient-equivalent spelling,
splicing it between the unchanged prefix and suffix would shorten the whole
normal word.

This is the minimality step in Osin's proof of Lemma 5.1.  Applied to the
boundary arc and replacement word of a Greendlinger cut, it rules out a cut
whose opposite arc lies strictly inside one normal side.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

/-! ## Contiguous segments -/

/-- The half-open segment `[i,j)` of the chosen quotient-normal word. -/
noncomputable def quotientNormalSegment
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) (i j : ℕ) : List G :=
  (quotientNormalWord D q hq y).drop i |>.take (j - i)

/-- A normal word splits as its prefix, the segment `[i,j)`, and its suffix. -/
theorem quotientNormalWord_eq_take_append_segment_append_drop
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) {i j : ℕ}
    (hij : i ≤ j) :
    quotientNormalWord D q hq y =
      (quotientNormalWord D q hq y).take i ++
        quotientNormalSegment D q hq y i j ++
          (quotientNormalWord D q hq y).drop j := by
  let word := quotientNormalWord D q hq y
  have hdrop : (word.drop i).drop (j - i) = word.drop j := by
    rw [List.drop_drop]
    congr 1
    omega
  calc
    word = word.take i ++ word.drop i := (List.take_append_drop i word).symm
    _ = word.take i ++
        ((word.drop i).take (j - i) ++ (word.drop i).drop (j - i)) := by
      exact congrArg (word.take i ++ ·)
        (List.take_append_drop (j - i) (word.drop i)).symm
    _ = word.take i ++ (word.drop i).take (j - i) ++ word.drop j := by
      rw [hdrop, List.append_assoc]
    _ = word.take i ++ quotientNormalSegment D q hq y i j ++
        word.drop j := rfl

/-- A segment ending before the end of the word has its expected length. -/
theorem quotientNormalSegment_length
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) {i j : ℕ}
    (hij : i ≤ j)
    (hj : j ≤ (quotientNormalWord D q hq y).length) :
    (quotientNormalSegment D q hq y i j).length = j - i := by
  rw [quotientNormalSegment, List.length_take, List.length_drop]
  omega

/-- Every segment of a normal word is legal over the source alphabet. -/
theorem quotientNormalSegment_isWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) (i j : ℕ) :
    IsWord D.alphabet.carrier (quotientNormalSegment D q hq y i j)
      (quotientNormalSegment D q hq y i j).prod := by
  exact isWord_take (isWord_drop
    (quotientNormalWord.isWord D q hq y) i) (j - i)

/-! ## Splicing a proposed replacement -/

/-- Replacing `[i,j)` by another legal word gives a legal source word. -/
theorem isWord_take_append_append_drop
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) (i j : ℕ)
    {replacement : List G}
    (hreplacement : IsWord D.alphabet.carrier replacement replacement.prod) :
    IsWord D.alphabet.carrier
      ((quotientNormalWord D q hq y).take i ++ replacement ++
        (quotientNormalWord D q hq y).drop j)
      (((quotientNormalWord D q hq y).take i ++ replacement ++
        (quotientNormalWord D q hq y).drop j).prod) := by
  have hlegal := isWord_append
    (isWord_take (quotientNormalWord.isWord D q hq y) i)
    (isWord_append hreplacement
      (isWord_drop (quotientNormalWord.isWord D q hq y) j))
  simpa only [List.append_assoc, List.prod_append, mul_assoc] using hlegal

/-- A quotient-equivalent segment replacement preserves the quotient value of
the complete word. -/
theorem map_prod_take_append_replacement_append_drop
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) {i j : ℕ}
    (hij : i ≤ j) {replacement : List G}
    (hmap : q replacement.prod =
      q (quotientNormalSegment D q hq y i j).prod) :
    q (((quotientNormalWord D q hq y).take i ++ replacement ++
      (quotientNormalWord D q hq y).drop j).prod) = y := by
  let word := quotientNormalWord D q hq y
  let segment := quotientNormalSegment D q hq y i j
  have hsplit : word = word.take i ++ segment ++ word.drop j :=
    quotientNormalWord_eq_take_append_segment_append_drop
      D q hq y hij
  have hwordMap : q word.prod = y := quotientNormalWord.map_prod D q hq y
  simp only [List.prod_append, map_mul]
  rw [hmap]
  have hprod : word.prod =
      (word.take i).prod * segment.prod * (word.drop j).prod := by
    have := congrArg List.prod hsplit
    simpa only [List.prod_append] using this
  rw [← map_mul, ← map_mul, ← hprod]
  exact hwordMap

/-! ## Quotient-minimality of every segment -/

/-- Every legal word with the same quotient value as `[i,j)` has at least the
segment's length. -/
theorem quotientNormalSegment_length_le
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) {i j : ℕ}
    (hij : i ≤ j)
    (hj : j ≤ (quotientNormalWord D q hq y).length)
    {replacement : List G}
    (hreplacement : IsWord D.alphabet.carrier replacement replacement.prod)
    (hmap : q replacement.prod =
      q (quotientNormalSegment D q hq y i j).prod) :
    (quotientNormalSegment D q hq y i j).length ≤ replacement.length := by
  let word := quotientNormalWord D q hq y
  let segment := quotientNormalSegment D q hq y i j
  let candidate := word.take i ++ replacement ++ word.drop j
  have hcandidateWord : IsWord D.alphabet.carrier candidate candidate.prod :=
    isWord_take_append_append_drop D q hq y i j hreplacement
  have hcandidateMap : q candidate.prod = y :=
    map_prod_take_append_replacement_append_drop
      D q hq y hij hmap
  have hminimal : word.length ≤ candidate.length :=
    quotientNormalWord.length_le D q hq y hcandidateWord hcandidateMap
  have hi : i ≤ word.length := le_trans hij hj
  have hjword : j ≤ word.length := hj
  have hsegment :
      (quotientNormalSegment D q hq y i j).length = j - i :=
    quotientNormalSegment_length D q hq y hij hj
  dsimp only [candidate] at hminimal
  simp only [List.length_append, List.length_drop] at hminimal
  rw [List.length_take_of_le hi] at hminimal
  have hwordLength :
      word.length = (i + (j - i)) + (word.length - j) := by
    omega
  have hsum :
      (i + (j - i)) + (word.length - j) ≤
        (i + replacement.length) + (word.length - j) := by
    calc
      (i + (j - i)) + (word.length - j) = word.length :=
        hwordLength.symm
      _ ≤ (i + replacement.length) + (word.length - j) := hminimal
  have hmiddle : i + (j - i) ≤ i + replacement.length :=
    Nat.add_le_add_iff_right.mp hsum
  rw [hsegment]
  exact Nat.add_le_add_iff_left.mp hmiddle

/-- No strictly shorter legal word can have the quotient value of a normal
segment. -/
theorem not_length_lt_of_map_prod_eq_segment
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) {i j : ℕ}
    (hij : i ≤ j)
    (hj : j ≤ (quotientNormalWord D q hq y).length)
    {replacement : List G}
    (hreplacement : IsWord D.alphabet.carrier replacement replacement.prod)
    (hmap : q replacement.prod =
      q (quotientNormalSegment D q hq y i j).prod) :
    ¬ replacement.length <
      (quotientNormalSegment D q hq y i j).length := by
  have hle := quotientNormalSegment_length_le D q hq y hij hj
    hreplacement hmap
  omega

/-! ## Decomposition form -/

/-- A contiguous sublist displayed by a three-part decomposition is shortest
among legal source words with the same quotient value. -/
theorem quotientNormalSublist_length_le
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q)
    {prefix segment suffix replacement : List G}
    (hsplit : quotientNormalWord D q hq y =
      prefix ++ segment ++ suffix)
    (hreplacement :
      IsWord D.alphabet.carrier replacement replacement.prod)
    (hmap : q replacement.prod = q segment.prod) :
    segment.length ≤ replacement.length := by
  let normal := quotientNormalWord D q hq y
  let candidate := prefix ++ replacement ++ suffix
  have hnormal : IsWord D.alphabet.carrier normal normal.prod :=
    quotientNormalWord.isWord D q hq y
  have hcandidate :
      IsWord D.alphabet.carrier candidate candidate.prod := by
    refine ⟨?_, rfl⟩
    intro x hx
    have hxparts : x ∈ prefix ∨ x ∈ replacement ∨ x ∈ suffix := by
      simpa only [candidate, List.mem_append] using hx
    rcases hxparts with hxprefix | hxreplacement | hxsuffix
    · apply hnormal.letters x
      rw [hsplit]
      exact List.mem_append_left _ (List.mem_append_left _ hxprefix)
    · exact hreplacement.letters x hxreplacement
    · apply hnormal.letters x
      rw [hsplit]
      exact List.mem_append_right _ hxsuffix
  have hcandidateMap : q candidate.prod = y := by
    have hnormalMap : q normal.prod = y :=
      quotientNormalWord.map_prod D q hq y
    have hnormalProd :
        normal.prod = prefix.prod * segment.prod * suffix.prod := by
      have := congrArg List.prod hsplit
      simpa only [List.prod_append] using this
    simp only [candidate, List.prod_append, map_mul]
    rw [hmap, ← map_mul, ← map_mul, ← hnormalProd]
    exact hnormalMap
  have hminimal : normal.length ≤ candidate.length :=
    quotientNormalWord.length_le D q hq y hcandidate hcandidateMap
  have hnormalLength := congrArg List.length hsplit
  simp only [candidate, List.length_append] at hminimal hnormalLength
  omega

/-- A displayed contiguous sublist has no strictly shorter legal
quotient-equivalent replacement. -/
theorem not_length_lt_of_map_prod_eq_normalSublist
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q)
    {prefix segment suffix replacement : List G}
    (hsplit : quotientNormalWord D q hq y =
      prefix ++ segment ++ suffix)
    (hreplacement :
      IsWord D.alphabet.carrier replacement replacement.prod)
    (hmap : q replacement.prod = q segment.prod) :
    ¬ replacement.length < segment.length := by
  have hle := quotientNormalSublist_length_le D q hq y hsplit
    hreplacement hmap
  omega

/-! ## Model check -/

/-- Every segment in the one-point target model is empty because its complete
normal word is empty. -/
theorem quotientNormalSegment_trivialTarget
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* PUnit)
    (hq : Function.Surjective q) (y : PUnit) (i j : ℕ) :
    quotientNormalSegment D q hq y i j = [] := by
  rw [quotientNormalSegment, quotientNormalWord_trivialTarget D q hq y]
  simp

end HullSC
end GroupApproximation
