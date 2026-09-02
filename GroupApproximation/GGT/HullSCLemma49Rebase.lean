import GroupApproximation.GGT.HullSCLemma49EmbeddedArc
import GroupApproximation.GGT.HullSCLemma49ShortPower
import GroupApproximation.Sofic.PeriodicOverlap

/-!
# Rebasing cyclic power arcs in Hull's Lemma 4.9

An exterior contiguity arc supplied by source Gr0 is cyclic in the outer
boundary.  Hull's shortening argument may choose its basepoint at the start of
that arc.  This module proves that operation on the formal power diagram.

First, rotating a repeated list is the repetition of the rotated period.  A
rotation of a geodesic shortest quotient-conjugacy representative is another
geodesic shortest representative.  Its power is an ordinary conjugate of the
original power, so normality and the least-area construction supply a reduced
oriented power diagram with that rotated boundary word.  The cyclic embedded
arc then becomes a based `Lemma49RelativeGreendlingerCell` with empty prefix,
without changing any relator, connector, or length estimate.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-! ## Rotating repeated lists -/

/-- Moving a prefix `a` through `n` copies of `a ++ b` changes every block to
`b ++ a`. -/
theorem lemma49BoundaryPower_append_left_comm
    {Alpha : Type*} (a b : List Alpha) : ∀ n : ℕ,
    lemma49BoundaryPower (a ++ b) n ++ a =
      a ++ lemma49BoundaryPower (b ++ a) n
  | 0 => by simp [lemma49BoundaryPower]
  | n + 1 => by
      rw [lemma49BoundaryPower, lemma49BoundaryPower,
        List.append_assoc, lemma49BoundaryPower_append_left_comm a b n]
      simp only [List.append_assoc]

/-- For a rotation index within one period, rotating a positive repeated word
rotates each period by the same index. -/
theorem lemma49BoundaryPower_rotate_of_le
    {Alpha : Type*} (word : List Alpha) {n start : ℕ}
    (hn : 0 < n) (hstart : start ≤ word.length) :
    (lemma49BoundaryPower word n).rotate start =
      lemma49BoundaryPower (word.rotate start) n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hstartPower : start ≤
      (lemma49BoundaryPower word (m + 1)).length := by
    rw [lemma49BoundaryPower_length]
    nlinarith
  rw [List.rotate_eq_drop_append_take hstartPower,
    lemma49BoundaryPower]
  have hdrop :
      (word ++ lemma49BoundaryPower word m).drop start =
        word.drop start ++ lemma49BoundaryPower word m := by
    exact List.drop_append_of_le_length hstart
  have htake :
      (word ++ lemma49BoundaryPower word m).take start = word.take start := by
    exact List.take_append_of_le_length hstart
  rw [hdrop, htake, List.rotate_eq_drop_append_take hstart,
    lemma49BoundaryPower]
  have hcomm := lemma49BoundaryPower_append_left_comm
    (word.take start) (word.drop start) m
  have hword : word.take start ++ word.drop start = word :=
    List.take_append_drop start word
  rw [hword] at hcomm
  calc
    word.drop start ++ lemma49BoundaryPower word m ++ word.take start =
        word.drop start ++
          (word.take start ++ lemma49BoundaryPower
            (word.drop start ++ word.take start) m) := by
      simpa only [List.append_assoc] using
        congrArg (fun z => word.drop start ++ z) hcomm
    _ = (word.drop start ++ word.take start) ++
        lemma49BoundaryPower (word.drop start ++ word.take start) m := by
      rw [List.append_assoc]

/-- A repeated word is fixed by rotation through one complete period. -/
theorem lemma49BoundaryPower_rotate_period
    {Alpha : Type*} (word : List Alpha) (n : ℕ) :
    (lemma49BoundaryPower word n).rotate word.length =
      lemma49BoundaryPower word n := by
  rw [lemma49BoundaryPower_eq_flatten_replicate]
  exact PeriodicOverlap.rotate_length_flatten_replicate n word

/-- Rotating by a multiple of one period fixes the repeated word. -/
theorem lemma49BoundaryPower_rotate_period_mul
    {Alpha : Type*} (word : List Alpha) (n multiple : ℕ) :
    (lemma49BoundaryPower word n).rotate (word.length * multiple) =
      lemma49BoundaryPower word n := by
  exact PeriodicOverlap.rotate_eq_self_mul
    (lemma49BoundaryPower_rotate_period word n) multiple

/-- Rotating a positive repeated word at an arbitrary cyclic position is the
positive repetition of the period rotated at that position. -/
theorem lemma49BoundaryPower_rotate
    {Alpha : Type*} (word : List Alpha) {n : ℕ} (hn : 0 < n)
    (start : ℕ) :
    (lemma49BoundaryPower word n).rotate start =
      lemma49BoundaryPower (word.rotate start) n := by
  by_cases hword : word = []
  · subst word
    have hnil : ∀ k : ℕ,
        lemma49BoundaryPower ([] : List Alpha) k = [] := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [lemma49BoundaryPower, ih, List.nil_append]
    simp only [hnil, List.rotate_nil]
  · have hlength : 0 < word.length := List.length_pos_of_ne_nil hword
    let reducedStart := start % word.length
    have hreduced : reducedStart ≤ word.length :=
      (Nat.mod_lt start hlength).le
    have hdivision : word.length * (start / word.length) + reducedStart =
        start := by
      dsimp [reducedStart]
      rw [Nat.mul_comm]
      exact Nat.div_add_mod' start word.length
    calc
      (lemma49BoundaryPower word n).rotate start =
          (lemma49BoundaryPower word n).rotate
            (word.length * (start / word.length) + reducedStart) := by
        rw [hdivision]
      _ = ((lemma49BoundaryPower word n).rotate
            (word.length * (start / word.length))).rotate reducedStart := by
        rw [List.rotate_rotate]
      _ = (lemma49BoundaryPower word n).rotate reducedStart := by
        rw [lemma49BoundaryPower_rotate_period_mul]
      _ = lemma49BoundaryPower (word.rotate reducedStart) n :=
        lemma49BoundaryPower_rotate_of_le word hn hreduced
      _ = lemma49BoundaryPower (word.rotate start) n := by
        dsimp [reducedStart]
        rw [List.rotate_mod]

/-! ## Rotating shortest representatives -/

/-- A rotation of a shortest geodesic period is ordinarily conjugate to the
original period element. -/
theorem conjugateModulo_listVal_rotate
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} (N : Subgroup G)
    {g : G} {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    (start : ℕ) :
    ConjugateModulo N g (GGT.RelLetter.listVal (word.rotate start)) := by
  by_cases hwordNil : word = []
  · subst word
    have hg : g = 1 := by
      simpa [GGT.RelLetter.listVal_nil] using hword.2.1.symm
    subst g
    exact ConjugateModulo.refl N 1
  · let reducedStart := start % word.length
    have hlength : 0 < word.length := List.length_pos_of_ne_nil hwordNil
    have hreduced : reducedStart ≤ word.length :=
      (Nat.mod_lt start hlength).le
    let prefixValue := GGT.RelLetter.listVal (word.take reducedStart)
    refine ⟨prefixValue⁻¹, 1, N.one_mem, ?_⟩
    have hvalue : GGT.RelLetter.listVal word = g := by
      simpa only [one_mul] using hword.2.1
    rw [← List.rotate_mod word start,
      RelWord.listVal_rotate word hreduced, hvalue]
    simp only [mul_one, inv_inv]
    rfl

/-- Rotation preserves shortestness in a quotient conjugacy class because it
preserves the geodesic word length. -/
theorem isShortestModuloConjugacy_listVal_rotate
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    (start : ℕ) :
    IsShortestModuloConjugacy D.alphabet.carrier N
      (GGT.RelLetter.listVal (word.rotate start)) := by
  let rotated := GGT.RelLetter.listVal (word.rotate start)
  have hconj : ConjugateModulo N g rotated :=
    conjugateModulo_listVal_rotate N hword start
  have hrotatedGeo : GGT.OsinComponents.IsGeodesicWord D 1 rotated
      (word.rotate start) := by
    by_cases hwordNil : word = []
    · subst word
      have hg : g = 1 := by
        simpa [GGT.RelLetter.listVal_nil] using hword.2.1.symm
      subst g
      simpa [rotated, GGT.RelLetter.listVal_nil] using hword
    · have hlength : 0 < word.length := List.length_pos_of_ne_nil hwordNil
      have hbase := isGeodesicWord_rotate_of_shortestModuloConjugacy
        D N hshort hword (Nat.mod_lt start hlength).le
      simpa only [List.rotate_mod] using hbase
  have hnorm : wordNorm D.alphabet.carrier rotated =
      wordNorm D.alphabet.carrier g := by
    have hwordLength : word.length = wordNorm D.alphabet.carrier g := by
      simpa only [wordDist_one_left] using hword.2.2
    have hrotatedLength : (word.rotate start).length =
        wordNorm D.alphabet.carrier rotated := by
      simpa only [wordDist_one_left] using hrotatedGeo.2.2
    rw [← hrotatedLength, List.length_rotate, hwordLength]
  intro candidate hcandidate
  rw [hnorm]
  exact hshort candidate (hconj.trans hcandidate)

/-! ## A fresh diagram with the rotated boundary -/

/-- The conjugate power has a least-area oriented diagram whose geodesic
period is the chosen rotation. -/
theorem exists_rotated_lemma49GeodesicPowerDiagram
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n : ℕ}
    (Z : Lemma49GeodesicPowerDiagram D v g n)
    (hshort : IsShortestModuloConjugacy D.alphabet.carrier
      (Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)) g)
    (start : ℕ) :
    ∃ rotated : G,
      ∃ Zrot : Lemma49GeodesicPowerDiagram D v rotated n,
        ∃ conjugator : G,
        Zrot.boundaryWord = Z.boundaryWord.rotate start ∧
          rotated = conjugator⁻¹ * g * conjugator ∧
          ConjugateModulo
            (Subgroup.normalClosure
              ({GGT.RelLetter.listVal v} : Set G)) g rotated ∧
          IsShortestModuloConjugacy D.alphabet.carrier
            (Subgroup.normalClosure
              ({GGT.RelLetter.listVal v} : Set G)) rotated := by
  let N : Subgroup G :=
    Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)
  letI : N.Normal := Subgroup.normalClosure_normal
  let rotatedWord := Z.boundaryWord.rotate start
  let rotated := GGT.RelLetter.listVal rotatedWord
  have hconj : ConjugateModulo N g rotated := by
    exact conjugateModulo_listVal_rotate N Z.boundary_geodesic start
  have hpowMem : rotated ^ n ∈ N :=
    hconj.pow_mem Z.power_mem_normalClosure
  have hwordNe : Z.boundaryWord ≠ [] := by
    intro hnil
    have hg : g = 1 := by
      have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
        simpa only [one_mul] using Z.boundary_geodesic.2.1
      rw [hnil, GGT.RelLetter.listVal_nil] at hvalue
      exact hvalue.symm
    exact Z.power_ne_one (by simp [hg])
  let reducedStart := start % Z.boundaryWord.length
  have hlength : 0 < Z.boundaryWord.length :=
    List.length_pos_of_ne_nil hwordNe
  have hreduced : reducedStart ≤ Z.boundaryWord.length :=
    (Nat.mod_lt start hlength).le
  let prefixValue :=
    GGT.RelLetter.listVal (Z.boundaryWord.take reducedStart)
  have hrotateValue : rotated = prefixValue⁻¹ * g * prefixValue := by
    dsimp [rotated, rotatedWord, prefixValue, reducedStart]
    rw [← List.rotate_mod Z.boundaryWord start,
      RelWord.listVal_rotate Z.boundaryWord hreduced]
    have hvalue : GGT.RelLetter.listVal Z.boundaryWord = g := by
      simpa only [one_mul] using Z.boundary_geodesic.2.1
    rw [hvalue]
  have hpowNe : rotated ^ n ≠ 1 := by
    intro hrotatedOne
    apply Z.power_ne_one
    have hconjugatePower :
        rotated ^ n = prefixValue⁻¹ * g ^ n * prefixValue := by
      rw [hrotateValue]
      simpa only [inv_inv] using
        (conj_pow :
          (prefixValue⁻¹ * g * (prefixValue⁻¹)⁻¹) ^ n =
            prefixValue⁻¹ * g ^ n * (prefixValue⁻¹)⁻¹)
    rw [hconjugatePower] at hrotatedOne
    calc
      g ^ n = prefixValue *
          (prefixValue⁻¹ * g ^ n * prefixValue) * prefixValue⁻¹ := by
        group
      _ = 1 := by rw [hrotatedOne]; simp
  obtain ⟨Zreduced⟩ := exists_lemma49ReducedPowerDiagram
    Z.exponent_pos hpowMem hpowNe
  obtain ⟨Zoriented⟩ := Zreduced.exists_oriented
  have hrotatedGeo : GGT.OsinComponents.IsGeodesicWord D 1 rotated
      rotatedWord := by
    have hbase := isGeodesicWord_rotate_of_shortestModuloConjugacy D N
      hshort Z.boundary_geodesic hreduced
    simpa only [rotated, rotatedWord, reducedStart, List.rotate_mod] using hbase
  let Zrot : Lemma49GeodesicPowerDiagram D v rotated n := {
    toLemma49OrientedPowerDiagram := Zoriented
    boundaryWord := rotatedWord
    boundary_geodesic := hrotatedGeo }
  refine ⟨rotated, Zrot, prefixValue, rfl, hrotateValue, hconj, ?_⟩
  exact isShortestModuloConjugacy_listVal_rotate N hshort
    Z.boundary_geodesic start

/-! ## Rebasing an embedded cyclic exterior arc -/

/-- Every cyclic embedded exterior arc can be based at its initial point in a
rotated shortest power diagram. -/
theorem Lemma49EmbeddedExteriorArc.exists_rebasedGreendlingerCell
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (E : Lemma49EmbeddedExteriorArc D v g n eps mu Z)
    (hshort : IsShortestModuloConjugacy D.alphabet.carrier
      (Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G)) g) :
    ∃ rotated : G,
      ∃ Zrot : Lemma49GeodesicPowerDiagram D v rotated n,
        ∃ conjugator : G,
        rotated = conjugator⁻¹ * g * conjugator ∧
          ConjugateModulo
            (Subgroup.normalClosure
              ({GGT.RelLetter.listVal v} : Set G)) g rotated ∧
          Zrot.boundaryWord = Z.boundaryWord.rotate E.boundaryStart ∧
          IsShortestModuloConjugacy D.alphabet.carrier
            (Subgroup.normalClosure
              ({GGT.RelLetter.listVal v} : Set G)) rotated ∧
          Nonempty (Lemma49RelativeGreendlingerCell
            D v rotated n eps mu Zrot) := by
  obtain ⟨rotated, Zrot, conjugator, hword, hconjugate, hconj, hshortRot⟩ :=
    exists_rotated_lemma49GeodesicPowerDiagram D Z hshort E.boundaryStart
  have hpower : lemma49BoundaryPower Zrot.boundaryWord n =
      E.boundaryArc ++ E.boundaryAfter := by
    rw [hword]
    rw [← lemma49BoundaryPower_rotate Z.boundaryWord Z.exponent_pos
      E.boundaryStart]
    exact E.boundary_rotation_decomposition
  let contiguity : RelativeBoundaryContiguity D eps
      ((lemma49BoundaryPower Zrot.boundaryWord n).map GGT.RelLetter.val)
      E.relator := {
    exterior := E.exterior
    remainder := E.remainder
    relator_decomposition := E.relator_decomposition
    boundaryBefore := []
    boundaryArc := E.boundaryArc.map GGT.RelLetter.val
    boundaryAfter := E.boundaryAfter.map GGT.RelLetter.val
    boundary_decomposition := by
      have h := congrArg (List.map GGT.RelLetter.val) hpower
      simpa only [List.map_append, List.nil_append] using h
    leftSide := E.leftSide
    rightSide := E.rightSide
    leftSide_admissible := E.leftSide_admissible
    rightSide_admissible := E.rightSide_admissible
    leftSide_short := E.leftSide_short
    rightSide_short := E.rightSide_short
    exterior_value := by
      simpa only [GGT.RelLetter.listVal] using E.exterior_value }
  let C : Lemma49RelativeGreendlingerCell D v rotated n eps mu Zrot := {
    relator := E.relator
    relator_mem := E.relator_mem
    contiguity := contiguity
    boundaryBefore := []
    boundaryArc := E.boundaryArc
    boundaryAfter := E.boundaryAfter
    boundary_decomposition := by simpa only [List.nil_append] using hpower
    boundaryArc_value := rfl
    exterior_large := E.exterior_large }
  exact ⟨rotated, Zrot, conjugator, hconjugate, hconj, hword, hshortRot, ⟨C⟩⟩

end HullSC
end GroupApproximation
