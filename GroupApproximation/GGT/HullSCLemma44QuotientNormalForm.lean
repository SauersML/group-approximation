import GroupApproximation.GGT.HullSCLemma44PrefixRelGenSet
import GroupApproximation.GGT.OsinGeodesicWord

/-!
# Shortest source spellings for quotient elements

Osin's proof of Lemma 5.1 compares quotient paths by choosing, for each
quotient element, a shortest spelling among all of its source lifts.  This
file constructs that spelling for an arbitrary surjection from a group with a
relative generating set.

The chosen word is geodesic in the source relative Cayley graph and is minimal
among every source word whose value has the prescribed quotient image.  Its
mapped prefix vertices form a path in the prefix quotient with unit steps.
These are the normal paths used when the Greendlinger certificate is applied
to a triangle of shortest lifts.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u v w

/-! ## The least spelling length -/

/-- A legal source word of a specified length whose value maps to `y`. -/
def HasQuotientSpellingAtLength
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q) (y : Q) (n : ℕ) : Prop :=
  ∃ word : List G,
    IsWord D.alphabet.carrier word word.prod ∧
      q word.prod = y ∧ word.length = n

/-- Surjectivity makes the set of source spelling lengths nonempty. -/
theorem exists_hasQuotientSpellingAtLength
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) :
    ∃ n : ℕ, HasQuotientSpellingAtLength D q y n := by
  obtain ⟨g, hg⟩ := hq y
  obtain ⟨word, hword⟩ := exists_isWord D.alphabet.symmetricGenerating g
  refine ⟨word.length, word, ?_, ?_, rfl⟩
  · exact ⟨hword.letters, rfl⟩
  · rw [hword.prod_eq, hg]

/-- The least length of a legal source word mapping to `y`. -/
noncomputable def quotientSpellingLength
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) : ℕ := by
  classical
  exact Nat.find (exists_hasQuotientSpellingAtLength D q hq y)

/-- A chosen shortest legal source word mapping to `y`. -/
noncomputable def quotientNormalWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) : List G := by
  classical
  exact Classical.choose
    (Nat.find_spec (exists_hasQuotientSpellingAtLength D q hq y))

namespace quotientNormalWord

/-- The chosen normal word is legal over the source relative alphabet. -/
theorem isWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) :
    IsWord D.alphabet.carrier (quotientNormalWord D q hq y)
      (quotientNormalWord D q hq y).prod := by
  classical
  exact (Classical.choose_spec
    (Nat.find_spec (exists_hasQuotientSpellingAtLength D q hq y))).1

/-- The value of the chosen normal word maps to the prescribed element. -/
theorem map_prod
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) :
    q (quotientNormalWord D q hq y).prod = y := by
  classical
  exact (Classical.choose_spec
    (Nat.find_spec (exists_hasQuotientSpellingAtLength D q hq y))).2.1

/-- The chosen word has the least spelling length selected by `Nat.find`. -/
theorem length_eq
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) :
    (quotientNormalWord D q hq y).length =
      quotientSpellingLength D q hq y := by
  classical
  exact (Classical.choose_spec
    (Nat.find_spec (exists_hasQuotientSpellingAtLength D q hq y))).2.2

/-- No legal source spelling of the same quotient element is shorter than the
chosen normal word. -/
theorem length_le
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q)
    {word : List G}
    (hword : IsWord D.alphabet.carrier word word.prod)
    (hmap : q word.prod = y) :
    (quotientNormalWord D q hq y).length ≤ word.length := by
  classical
  rw [length_eq]
  exact Nat.find_min'
    (exists_hasQuotientSpellingAtLength D q hq y)
    ⟨word, hword, hmap, rfl⟩

/-- The chosen quotient-normal word is also geodesic between the identity and
its source value. -/
theorem isGeodesicWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (y : Q) :
    IsGeodesicWord D.alphabet.carrier
      (quotientNormalWord D q hq y)
      (quotientNormalWord D q hq y).prod := by
  let word := quotientNormalWord D q hq y
  have hword : IsWord D.alphabet.carrier word word.prod :=
    isWord D q hq y
  have hnormUpper : wordNorm D.alphabet.carrier word.prod ≤ word.length :=
    wordNorm_le_length hword
  obtain ⟨geo, hgeo⟩ :=
    exists_isGeodesicWord D.alphabet.symmetricGenerating word.prod
  have hgeoWord : IsWord D.alphabet.carrier geo geo.prod :=
    ⟨hgeo.isWord.letters, rfl⟩
  have hgeoMap : q geo.prod = y := by
    rw [hgeo.isWord.prod_eq, ← map_prod D q hq y]
  have hminimal : word.length ≤ geo.length :=
    length_le D q hq y hgeoWord hgeoMap
  have hnormLower : word.length ≤
      wordNorm D.alphabet.carrier word.prod := by
    rw [← hgeo.length_eq]
    exact hminimal
  exact ⟨hword, Nat.le_antisymm hnormLower hnormUpper⟩

/-- The identity has the empty quotient-normal spelling. -/
theorem eq_nil_of_target_eq_one
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) {y : Q} (hy : y = 1) :
    quotientNormalWord D q hq y = [] := by
  subst y
  have hempty : IsWord D.alphabet.carrier ([] : List G) [].prod := by
    exact ⟨by simp, rfl⟩
  have hmap : q ([].prod : G) = (1 : Q) := by simp
  have hlength := length_le D q hq (1 : Q) hempty hmap
  simp only [List.length_nil, Nat.le_zero] at hlength
  exact List.length_eq_zero_iff.mp hlength

end quotientNormalWord

/-! ## The mapped normal path -/

/-- The vertex at time `i` on the mapped shortest-lift path from `x` to `y`. -/
noncomputable def quotientNormalPath
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y : Q) (i : ℕ) : Q :=
  x * q ((quotientNormalWord D q hq (x⁻¹ * y)).take i).prod

/-- The mapped normal path starts at its first endpoint. -/
theorem quotientNormalPath_zero
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y : Q) :
    quotientNormalPath D q hq x y 0 = x := by
  simp [quotientNormalPath]

/-- The mapped normal path ends at its second endpoint. -/
theorem quotientNormalPath_length
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (x y : Q) :
    quotientNormalPath D q hq x y
      (quotientNormalWord D q hq (x⁻¹ * y)).length = y := by
  rw [quotientNormalPath, List.take_length,
    quotientNormalWord.map_prod]
  group

/-- Each source letter of the chosen normal word maps to a legal letter in the
prefix quotient. -/
theorem map_mem_prefixQuotient_alphabet_of_mem_normalWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) (y : Q)
    {a : G} (ha : a ∈ quotientNormalWord D q hq y) :
    q a ∈ (D.prefixQuotient W hsc q hq).alphabet.carrier := by
  change q a ∈
    ((D.adjoinRelatorPrefixes W hsc).mapSurjective q hq).alphabet.carrier
  rw [GGT.RelGenSet.alphabet_carrier_mapSurjective]
  refine ⟨a, ?_, rfl⟩
  have hold : a ∈ D.alphabet.carrier :=
    (quotientNormalWord.isWord D q hq y).letters a ha
  rcases hold with hbase | hperipheral
  · exact Set.mem_union_left _ (Set.mem_union_left _ hbase)
  · exact Set.mem_union_right _ hperipheral

/-- Consecutive vertices of the mapped normal path are at prefix-quotient
distance at most one. -/
theorem quotientNormalPath_step
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    (x y : Q) (i : ℕ)
    (hi : i < (quotientNormalWord D q hq (x⁻¹ * y)).length) :
    wordDist (D.prefixQuotient W hsc q hq).alphabet.carrier
      (quotientNormalPath D q hq x y i)
      (quotientNormalPath D q hq x y (i + 1)) ≤ 1 := by
  let word := quotientNormalWord D q hq (x⁻¹ * y)
  have hletter : q word[i] ∈
      (D.prefixQuotient W hsc q hq).alphabet.carrier :=
    map_mem_prefixQuotient_alphabet_of_mem_normalWord
      D W hsc q hq (x⁻¹ * y) (List.getElem_mem hi)
  have hprod : (word.take (i + 1)).prod =
      (word.take i).prod * word[i] := by
    exact List.prod_take_succ word i hi
  rw [quotientNormalPath, quotientNormalPath, hprod, map_mul]
  have hleft := wordDist_left_invariant
    (D.prefixQuotient W hsc q hq).alphabet.carrier
    (x * q (word.take i).prod) 1 (q word[i])
  have hone := wordNorm_le_one_of_mem hletter
  calc
    wordDist (D.prefixQuotient W hsc q hq).alphabet.carrier
        (x * q (word.take i).prod)
        (x * (q (word.take i).prod * q word[i])) =
        wordDist (D.prefixQuotient W hsc q hq).alphabet.carrier
          1 (q word[i]) := by
      simpa only [mul_one, mul_assoc] using hleft
    _ = wordNorm (D.prefixQuotient W hsc q hq).alphabet.carrier
          (q word[i]) := wordDist_one_left _ _
    _ ≤ 1 := hone

/-! ## Degenerate check -/

/-- In the one-point target every chosen normal word is empty and every normal
path is constant. -/
theorem quotientNormalWord_trivialTarget
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (q : G →* PUnit)
    (hq : Function.Surjective q) (y : PUnit) :
    quotientNormalWord D q hq y = [] := by
  apply quotientNormalWord.eq_nil_of_target_eq_one D q hq
  exact Subsingleton.elim _ _

end HullSC
end GroupApproximation
