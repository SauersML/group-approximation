import GroupApproximation.GGT.DGOLemma421Statement

/-!
# Components of a DGO `W`-word

This module supplies the combinatorial first paragraph of the proof of
Dahmani--Guirardel--Osin Lemma 4.21.  Peripheral-letter positions are ordered,
condition (W1) gives at least one such position in every two consecutive
letters, and condition (W3) makes each peripheral letter a maximal singleton
component.  Successive peripheral positions are separated by either a trivial
path or one base edge, exactly the separator used in clause (b).
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-! ## Counting and locating peripheral letters -/

/-- The number of peripheral letters in a relative word. -/
def peripheralCount : List (RelLetter G Λ) → ℕ
  | [] => 0
  | RelLetter.base _ :: t => peripheralCount t
  | RelLetter.comp _ _ :: t => peripheralCount t + 1

/-- The number of base letters in a relative word. -/
def relativeBaseCount : List (RelLetter G Λ) → ℕ
  | [] => 0
  | RelLetter.base _ :: t => relativeBaseCount t + 1
  | RelLetter.comp _ _ :: t => relativeBaseCount t

omit [Group G] in
/-- Base and peripheral letters partition a relative word. -/
theorem relativeBaseCount_add_peripheralCount
    (word : List (RelLetter G Λ)) :
    relativeBaseCount word + peripheralCount word = word.length := by
  induction word with
  | nil => rfl
  | cons a t ih =>
      cases a <;> simp only [relativeBaseCount, peripheralCount,
        List.length_cons] at ih ⊢ <;> omega

/-- Positions carrying a peripheral letter. -/
def peripheralPositions : List (RelLetter G Λ) → Finset ℕ
  | [] => ∅
  | RelLetter.base _ :: t =>
      (peripheralPositions t).map ⟨Nat.succ, Nat.succ_injective⟩
  | RelLetter.comp _ _ :: t =>
      insert 0 ((peripheralPositions t).map
        ⟨Nat.succ, Nat.succ_injective⟩)

omit [Group G] in
/-- Membership in `peripheralPositions` is the existence of a peripheral
letter at that index. -/
theorem mem_peripheralPositions_iff
    {word : List (RelLetter G Λ)} {i : ℕ} :
    i ∈ peripheralPositions word ↔
      ∃ lam : Λ, ∃ g : G,
        word[i]? = some (RelLetter.comp lam g) := by
  induction word generalizing i with
  | nil => simp [peripheralPositions]
  | cons a t ih =>
      cases a with
      | base g =>
          cases i with
          | zero => simp [peripheralPositions]
          | succ i => simp [peripheralPositions, ih]
      | comp lam g =>
          cases i with
          | zero => simp [peripheralPositions]
          | succ i => simp [peripheralPositions, ih]

omit [Group G] in
/-- The position set has the expected cardinality. -/
theorem card_peripheralPositions (word : List (RelLetter G Λ)) :
    (peripheralPositions word).card = peripheralCount word := by
  induction word with
  | nil => rfl
  | cons a t ih =>
      cases a with
      | base g =>
          simpa [peripheralPositions, peripheralCount] using ih
      | comp lam g =>
          have hzero : 0 ∉ (peripheralPositions t).map
              ⟨Nat.succ, Nat.succ_injective⟩ := by simp
          rw [peripheralPositions, Finset.card_insert_of_notMem hzero,
            Finset.card_map, ih]
          rfl

omit [Group G] in
/-- Condition (W1) passes to the tail of a word. -/
theorem isWOne_tail {a : RelLetter G Λ} {t : List (RelLetter G Λ)}
    (h : WWord.IsWOne (a :: t)) : WWord.IsWOne t := by
  intro i x y hx hy
  exact h (i + 1) x y (by simpa using hx) (by simpa [Nat.add_assoc] using hy)

omit [Group G] in
/-- The W1 count, with the sharpened form for a word beginning in a peripheral
letter. -/
theorem relativeBaseCount_bounds_of_isWOne
    (word : List (RelLetter G Λ)) (h : WWord.IsWOne word) :
    relativeBaseCount word ≤ peripheralCount word + 1 ∧
      (match word with
      | RelLetter.comp _ _ :: _ =>
          relativeBaseCount word ≤ peripheralCount word
      | _ => True) := by
  induction word with
  | nil => simp [relativeBaseCount, peripheralCount]
  | cons a t ih =>
      have ht : WWord.IsWOne t := isWOne_tail h
      have hit := ih ht
      cases a with
      | comp lam g =>
          simp only [relativeBaseCount, peripheralCount]
          constructor <;> omega
      | base g =>
          constructor
          · cases t with
            | nil => simp [relativeBaseCount, peripheralCount]
            | cons b r =>
                cases b with
                | base y =>
                    exact False.elim (h 0 g y rfl rfl)
                | comp lam y =>
                    simp only [relativeBaseCount, peripheralCount] at hit ⊢
                    omega
          · trivial

omit [Group G] in
/-- A W1 word has at least half as many peripheral letters as its length,
up to the possible boundary base letter. -/
theorem length_le_two_mul_peripheralCount_add_one
    {word : List (RelLetter G Λ)} (h : WWord.IsWOne word) :
    word.length ≤ 2 * peripheralCount word + 1 := by
  have hpartition := relativeBaseCount_add_peripheralCount word
  have hbase := (relativeBaseCount_bounds_of_isWOne word h).1
  omega

/-! ## The ordered peripheral positions -/

/-- The `t`-th peripheral position, or the terminal position when `t` is out
of range. -/
noncomputable def peripheralPos (word : List (RelLetter G Λ)) (t : ℕ) : ℕ :=
  if ht : t < (peripheralPositions word).card then
    ((peripheralPositions word).orderIsoOfFin rfl ⟨t, ht⟩).1
  else word.length

omit [Group G] in
/-- An in-range ordered position belongs to the peripheral position set. -/
theorem peripheralPos_mem {word : List (RelLetter G Λ)} {t : ℕ}
    (ht : t < (peripheralPositions word).card) :
    peripheralPos word t ∈ peripheralPositions word := by
  unfold peripheralPos
  rw [dif_pos ht]
  exact ((peripheralPositions word).orderIsoOfFin rfl ⟨t, ht⟩).2

omit [Group G] in
/-- Ordered peripheral positions are strictly increasing. -/
theorem peripheralPos_lt {word : List (RelLetter G Λ)} {s t : ℕ}
    (ht : t < (peripheralPositions word).card) (hst : s < t) :
    peripheralPos word s < peripheralPos word t := by
  have hs : s < (peripheralPositions word).card := hst.trans ht
  unfold peripheralPos
  rw [dif_pos hs, dif_pos ht]
  exact (peripheralPositions word).orderIsoOfFin rfl |>.strictMono
    (show (⟨s, hs⟩ : Fin (peripheralPositions word).card) < ⟨t, ht⟩ by
      exact hst)

omit [Group G] in
/-- There is no peripheral position strictly between two successive ordered
positions. -/
theorem not_mem_peripheralPositions_between_succ
    {word : List (RelLetter G Λ)} {t z : ℕ}
    (ht : t + 1 < (peripheralPositions word).card)
    (hleft : peripheralPos word t < z)
    (hright : z < peripheralPos word (t + 1)) :
    z ∉ peripheralPositions word := by
  intro hz
  let E := (peripheralPositions word).orderIsoOfFin rfl
  let it : Fin (peripheralPositions word).card := ⟨t, by omega⟩
  let it1 : Fin (peripheralPositions word).card := ⟨t + 1, ht⟩
  let ez : peripheralPositions word := ⟨z, hz⟩
  have hitVal : (E it).val = peripheralPos word t := by
    unfold peripheralPos
    rw [dif_pos (show t < (peripheralPositions word).card by omega)]
  have hit1Val : (E it1).val = peripheralPos word (t + 1) := by
    unfold peripheralPos
    rw [dif_pos ht]
  have hleft' : E it < ez := by
    exact show (E it).val < ez.val from by
      change (E it).val < z
      calc
        (E it).val = peripheralPos word t := hitVal
        _ < z := hleft
  have hright' : ez < E it1 := by
    exact show ez.val < (E it1).val from by
      change z < (E it1).val
      calc
        z < peripheralPos word (t + 1) := hright
        _ = (E it1).val := hit1Val.symm
  have h1 : it < E.symm ez := by
    have := E.symm.strictMono hleft'
    simpa using this
  have h2 : E.symm ez < it1 := by
    have := E.symm.strictMono hright'
    simpa using this
  have h1v : t < (E.symm ez).val := h1
  have h2v : (E.symm ez).val < t + 1 := h2
  omega

omit [Group G] in
/-- The letter and peripheral index at an in-range ordered position. -/
theorem exists_read_peripheralPos {word : List (RelLetter G Λ)} {t : ℕ}
    (ht : t < (peripheralPositions word).card) :
    ∃ lam : Λ, ∃ g : G,
      word[peripheralPos word t]? = some (RelLetter.comp lam g) :=
  mem_peripheralPositions_iff.mp (peripheralPos_mem ht)

omit [Group G] in
/-- Successive peripheral positions differ by one or two. -/
theorem peripheralPos_succ_le_add_two {word : List (RelLetter G Λ)}
    (hW1 : WWord.IsWOne word) {t : ℕ}
    (ht : t + 1 < (peripheralPositions word).card) :
    peripheralPos word (t + 1) ≤ peripheralPos word t + 2 := by
  let i := peripheralPos word t
  let j := peripheralPos word (t + 1)
  have hij : i < j := peripheralPos_lt ht (by omega)
  by_contra hle
  have hfar : i + 2 < j := by omega
  have hi1Not : i + 1 ∉ peripheralPositions word :=
    not_mem_peripheralPositions_between_succ ht (by omega) (by omega)
  have hi2Not : i + 2 ∉ peripheralPositions word :=
    not_mem_peripheralPositions_between_succ ht (by omega) hfar
  have hjMem : j ∈ peripheralPositions word := peripheralPos_mem ht
  obtain ⟨lamj, gj, hjread⟩ := mem_peripheralPositions_iff.mp hjMem
  have hjlt : j < word.length := (List.getElem?_eq_some_iff.mp hjread).1
  have hi1lt : i + 1 < word.length := by omega
  have hi2lt : i + 2 < word.length := by omega
  have hi1base : ∃ x : G,
      word[i + 1]? = some (RelLetter.base x) := by
    cases hletter : word[i + 1]'hi1lt with
    | base x => exact ⟨x, by simpa [List.getElem?_eq_getElem hi1lt] using hletter⟩
    | comp lam g =>
        exfalso
        apply hi1Not
        apply mem_peripheralPositions_iff.mpr
        exact ⟨lam, g, by simpa [List.getElem?_eq_getElem hi1lt] using hletter⟩
  have hi2base : ∃ y : G,
      word[i + 2]? = some (RelLetter.base y) := by
    cases hletter : word[i + 2]'hi2lt with
    | base y => exact ⟨y, by simpa [List.getElem?_eq_getElem hi2lt] using hletter⟩
    | comp lam g =>
        exfalso
        apply hi2Not
        apply mem_peripheralPositions_iff.mpr
        exact ⟨lam, g, by simpa [List.getElem?_eq_getElem hi2lt] using hletter⟩
  obtain ⟨x, hx⟩ := hi1base
  obtain ⟨y, hy⟩ := hi2base
  exact hW1 (i + 1) x y hx (by simpa [Nat.add_assoc] using hy)

omit [Group G] in
/-- Successive peripheral positions have the separator printed in Lemma
4.21(b). -/
theorem baseEdgeOrTrivial_peripheralPos_succ {word : List (RelLetter G Λ)}
    (hW1 : WWord.IsWOne word) {t : ℕ}
    (ht : t + 1 < (peripheralPositions word).card) :
    BaseEdgeOrTrivial word (peripheralPos word t + 1)
      (peripheralPos word (t + 1)) := by
  have hlt : peripheralPos word t < peripheralPos word (t + 1) :=
    peripheralPos_lt ht (by omega)
  have hle := peripheralPos_succ_le_add_two hW1 ht
  by_cases heq : peripheralPos word (t + 1) = peripheralPos word t + 1
  · exact Or.inl heq
  · have heqTwo :
        peripheralPos word (t + 1) = peripheralPos word t + 2 := by omega
    apply Or.inr
    have hnextMem : peripheralPos word (t + 1) ∈ peripheralPositions word :=
      peripheralPos_mem ht
    obtain ⟨lam, g, hnextRead⟩ := mem_peripheralPositions_iff.mp hnextMem
    have hnextLt : peripheralPos word (t + 1) < word.length :=
      (List.getElem?_eq_some_iff.mp hnextRead).1
    have hmidLt : peripheralPos word t + 1 < word.length := by omega
    have hmidNot : peripheralPos word t + 1 ∉ peripheralPositions word :=
      not_mem_peripheralPositions_between_succ ht (by omega) (by omega)
    cases hletter : word[peripheralPos word t + 1]'hmidLt with
    | base x =>
        refine ⟨x, by omega, ?_⟩
        simpa [List.getElem?_eq_getElem hmidLt] using hletter
    | comp mu x =>
        exfalso
        apply hmidNot
        apply mem_peripheralPositions_iff.mpr
        exact ⟨mu, x,
          by simpa [List.getElem?_eq_getElem hmidLt] using hletter⟩

/-! ## W3 makes the peripheral letters singleton components -/

/-- A peripheral letter of a W3 word is a maximal singleton component. -/
theorem isComp_singleton_of_isWThree_read {D : RelGenSet G Λ}
    {word : List (RelLetter G Λ)} (hW3 : WWord.IsWThree D word)
    {i : ℕ} {lam : Λ} {g : G}
    (hread : word[i]? = some (RelLetter.comp lam g)) :
    IsComp lam word i (i + 1) := by
  have hi : i < word.length := (List.getElem?_eq_some_iff.mp hread).1
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro j hij hji hj
    have hjiEq : j = i := by omega
    subst j
    have hget : word[i]'hi = RelLetter.comp lam g := by
      exact (List.getElem?_eq_some_iff.mp hread).2
    rw [hget]
    rfl
  · intro j hij hj hcomp
    have hji : j + 1 = i := hij.symm
    cases hletter : word[j]'hj with
    | base x =>
        rw [hletter] at hcomp
        exact hcomp
    | comp mu x =>
        rw [hletter] at hcomp
        have hjread : word[j]? = some (RelLetter.comp mu x) := by
          simpa [List.getElem?_eq_getElem hj] using hletter
        have hne := hW3.1 j mu lam x g hjread (by simpa [hji] using hread)
        exact hne hcomp
  · intro hk hcomp
    cases hletter : word[i + 1]'hk with
    | base x =>
        rw [hletter] at hcomp
        exact hcomp
    | comp mu x =>
        rw [hletter] at hcomp
        have hkread : word[i + 1]? = some (RelLetter.comp mu x) := by
          simpa [List.getElem?_eq_getElem hk] using hletter
        have hne := hW3.1 i lam mu g x hread hkread
        exact hne hcomp.symm

/-- Every in-range ordered peripheral position of a W3 word is a singleton
component, with an existentially chosen label and letter. -/
theorem exists_isComp_peripheralPos {D : RelGenSet G Λ}
    {word : List (RelLetter G Λ)} (hW3 : WWord.IsWThree D word)
    {t : ℕ} (ht : t < (peripheralPositions word).card) :
    ∃ lam : Λ, ∃ g : G,
      word[peripheralPos word t]? = some (RelLetter.comp lam g) ∧
      IsComp lam word (peripheralPos word t) (peripheralPos word t + 1) := by
  obtain ⟨lam, g, hread⟩ := exists_read_peripheralPos ht
  exact ⟨lam, g, hread, isComp_singleton_of_isWThree_read hW3 hread⟩

end OsinComponents
end GGT
end GroupApproximation
