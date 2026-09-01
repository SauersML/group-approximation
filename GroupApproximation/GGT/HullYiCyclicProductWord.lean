import GroupApproximation.GGT.HullYiCyclicProductAssembly
import GroupApproximation.GGT.DGOLemma421Statement

/-!
# The relative word for Hull's cyclic `yi` products

Hull applies DGO Lemma 4.21(b) to powers of the word

`a₀ a₁ ⋯ aₖ₋₁`,

where `aᵢ ∈ E(fᵢ)` and the factors are indexed in their natural cyclic
order.  This file constructs that word from the `Fin`-indexed letter family and
proves the facts needed at the 4.21 call site: its value is the ordered product,
all letters are admissible in the elementary-closure cone-off, and every power
of the word satisfies (W1)--(W3) once its letters are deep.

No component match is assumed here.  The only remaining geometric input after
this module is DGO Lemma 4.21(b) itself (and the depth supplied when the powers
are selected).
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents

universe u w

variable {G : Type u} [Group G]

/-- A finite relative word whose `i`-th letter is placed in the peripheral
subgroup `index i`. -/
def indexedPeripheralWord {k : ℕ} {Λ : Type w} (index : Fin k → Λ)
    (a : Fin k → G) : List (RelLetter G Λ) :=
  List.ofFn (fun i ↦ RelLetter.comp (index i) (a i))

/-- The one-cycle relative word `a₀ a₁ ⋯ aₖ₋₁`, with the `i`-th
letter placed in the `i`-th peripheral subgroup. -/
def finPeripheralWord {k : ℕ} (a : Fin k → G) :
    List (RelLetter G (Fin k)) := indexedPeripheralWord id a

omit [Group G] in
@[simp] theorem length_finPeripheralWord {k : ℕ} (a : Fin k → G) :
    (finPeripheralWord a).length = k := by
  simp [finPeripheralWord, indexedPeripheralWord]

omit [Group G] in
@[simp] theorem finPeripheralWord_zero (a : Fin 0 → G) :
    finPeripheralWord a = [] := by
  simp [finPeripheralWord, indexedPeripheralWord]

omit [Group G] in
@[simp] theorem indexedPeripheralWord_zero {Λ : Type w}
    (index : Fin 0 → Λ) (a : Fin 0 → G) :
    indexedPeripheralWord index a = [] := by
  simp [indexedPeripheralWord]

omit [Group G] in
@[simp] theorem indexedPeripheralWord_succ {k : ℕ} {Λ : Type w}
    (index : Fin (k + 1) → Λ) (a : Fin (k + 1) → G) :
    indexedPeripheralWord index a = RelLetter.comp (index 0) (a 0) ::
      indexedPeripheralWord (fun i ↦ index i.succ) (fun i ↦ a i.succ) := by
  simp [indexedPeripheralWord, List.ofFn_succ]

omit [Group G] in
@[simp] theorem length_indexedPeripheralWord {k : ℕ} {Λ : Type w}
    (index : Fin k → Λ) (a : Fin k → G) :
    (indexedPeripheralWord index a).length = k := by
  simp [indexedPeripheralWord]

omit [Group G] in
@[simp] theorem getElem?_indexedPeripheralWord {k : ℕ} {Λ : Type w}
    (index : Fin k → Λ) (a : Fin k → G) (i : Fin k) :
    (indexedPeripheralWord index a)[i.val]? =
      some (RelLetter.comp (index i) (a i)) := by
  simp [indexedPeripheralWord]

/-- The ambient peripheral indices do not affect the value of the word. -/
@[simp] theorem listVal_indexedPeripheralWord :
    ∀ {k : ℕ} {Λ : Type w} (index : Fin k → Λ) (a : Fin k → G),
      RelLetter.listVal (indexedPeripheralWord index a) = orderedFinProduct a := by
  intro k Λ index a
  induction k with
  | zero => simp [indexedPeripheralWord, orderedFinProduct, RelLetter.listVal]
  | succ k ih =>
      rw [indexedPeripheralWord_succ, RelWord.listVal_cons]
      change a 0 * RelLetter.listVal
        (indexedPeripheralWord (fun i ↦ index i.succ) (fun i ↦ a i.succ)) = _
      rw [ih]
      rfl

/-- The relative word spells exactly the ordered product used by the algebraic
assembly. -/
@[simp] theorem listVal_finPeripheralWord {k : ℕ} (a : Fin k → G) :
    RelLetter.listVal (finPeripheralWord a) = orderedFinProduct a := by
  exact listVal_indexedPeripheralWord id a

omit [Group G] in
/-- Every letter in the cyclic word is the indicated peripheral letter. -/
theorem exists_eq_comp_of_mem_finPeripheralWord {k : ℕ} (a : Fin k → G)
    {c : RelLetter G (Fin k)} (hc : c ∈ finPeripheralWord a) :
    ∃ i : Fin k, c = RelLetter.comp i (a i) := by
  simpa [finPeripheralWord, indexedPeripheralWord, eq_comm] using hc

omit [Group G] in
/-- Membership in the ambient-index form. -/
theorem exists_eq_comp_of_mem_indexedPeripheralWord {k : ℕ} {Λ : Type w}
    (index : Fin k → Λ) (a : Fin k → G) {c : RelLetter G Λ}
    (hc : c ∈ indexedPeripheralWord index a) :
    ∃ i : Fin k, c = RelLetter.comp (index i) (a i) := by
  simpa [indexedPeripheralWord, eq_comm] using hc

/-- If the `i`-th element belongs to the `i`-th subgroup, the cyclic word is
admissible in that relative generating set. -/
theorem isLetter_finPeripheralWord (D : RelGenSet G (Fin k)) (a : Fin k → G)
    (ha : ∀ i, a i ∈ D.fam i) :
    ∀ c ∈ finPeripheralWord a, D.IsLetter c := by
  intro c hc
  obtain ⟨i, rfl⟩ := exists_eq_comp_of_mem_finPeripheralWord a hc
  exact ha i

omit [Group G] in
/-- The cyclic word contains no base letter. -/
theorem getElem?_finPeripheralWord_ne_base {k : ℕ} (a : Fin k → G)
    (j : ℕ) (y : G) :
    (finPeripheralWord a)[j]? ≠ some (RelLetter.base y) := by
  intro hj
  have hjlt : j < (finPeripheralWord a).length :=
    lt_length_of_getElem?_eq_some hj
  have hjmem : (finPeripheralWord a)[j]'hjlt ∈ finPeripheralWord a :=
    List.getElem_mem hjlt
  obtain ⟨i, hi⟩ := exists_eq_comp_of_mem_finPeripheralWord a hjmem
  have hget : (finPeripheralWord a)[j]? =
      some ((finPeripheralWord a)[j]'hjlt) := List.getElem?_eq_getElem hjlt
  rw [hget, hi] at hj
  simp at hj

omit [Group G] in
/-- The ambient-index word contains no base letter. -/
theorem getElem?_indexedPeripheralWord_ne_base {k : ℕ} {Λ : Type w}
    (index : Fin k → Λ) (a : Fin k → G) (j : ℕ) (y : G) :
    (indexedPeripheralWord index a)[j]? ≠ some (RelLetter.base y) := by
  intro hj
  have hjlt : j < (indexedPeripheralWord index a).length :=
    lt_length_of_getElem?_eq_some hj
  have hjmem : (indexedPeripheralWord index a)[j]'hjlt ∈
      indexedPeripheralWord index a := List.getElem_mem hjlt
  obtain ⟨i, hi⟩ := exists_eq_comp_of_mem_indexedPeripheralWord index a hjmem
  have hget : (indexedPeripheralWord index a)[j]? =
      some ((indexedPeripheralWord index a)[j]'hjlt) :=
    List.getElem?_eq_getElem hjlt
  rw [hget, hi] at hj
  simp at hj

omit [Group G] in
/-- Powers of the cyclic peripheral word satisfy (W1) automatically. -/
theorem isWOne_blockWord_finPeripheralWord {k : ℕ} (a : Fin (k + 1) → G)
    (n : ℕ) :
    WWord.IsWOne
      (OsinComponents.blockWord (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) n) := by
  exact isWOne_blockWord_of_noBase (Fin.last k)
    (getElem?_indexedPeripheralWord_ne_base
      (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
      (a (Fin.last k)) n

/-- Powers of the cyclic peripheral word satisfy (W2) when every letter is
outside the common relative-ball threshold. -/
theorem isWTwo_blockWord_finPeripheralWord (D : RelGenSet G (Fin (k + 1)))
    {C : ℕ} (a : Fin (k + 1) → G)
    (hdeep : ∀ i, a i ∉ D.relBall i C) (n : ℕ) :
    WWord.IsWTwo D C
      (OsinComponents.blockWord (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) n) := by
  apply isWTwo_blockWord_of_deep D (Fin.last k)
  · intro j mu g hj
    have hjlt : j <
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc)).length :=
      lt_length_of_getElem?_eq_some hj
    have hjmem := List.getElem_mem
      (l := indexedPeripheralWord (fun i ↦ i.castSucc)
        (fun i ↦ a i.castSucc)) hjlt
    obtain ⟨i, hi⟩ :=
      exists_eq_comp_of_mem_indexedPeripheralWord
        (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc) hjmem
    have hget := List.getElem?_eq_getElem hjlt
    rw [hget, hi] at hj
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hj
    rw [← hj.1, ← hj.2]
    exact hdeep i.castSucc
  · exact hdeep (Fin.last k)

/-- Powers of a cyclic peripheral word with at least two factors satisfy
(W3): adjacent letters have consecutive, hence distinct, `Fin` indices,
including at the last/prefix and wrap seams. -/
theorem isWThree_blockWord_finPeripheralWord (D : RelGenSet G (Fin (k + 1)))
    (hk : 1 ≤ k) (a : Fin (k + 1) → G) (n : ℕ) :
    WWord.IsWThree D
      (OsinComponents.blockWord (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) n) := by
  let pre : List (RelLetter G (Fin (k + 1))) :=
    indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc)
  apply isWThree_blockWord_of_cyclic D (Fin.last k)
  · intro hnil
    have hlen := congrArg List.length hnil
    simp at hlen
    omega
  · exact getElem?_indexedPeripheralWord_ne_base
      (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc)
  · intro j mu nu g₁ g₂ hj hj₁
    have hjlt : j < k := by
      have := lt_length_of_getElem?_eq_some hj
      simpa [pre] using this
    have hj₁lt : j + 1 < k := by
      have := lt_length_of_getElem?_eq_some hj₁
      simpa [pre] using this
    let i : Fin k := ⟨j, hjlt⟩
    let i₁ : Fin k := ⟨j + 1, hj₁lt⟩
    have hi := getElem?_indexedPeripheralWord
      (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc) i
    have hi₁ := getElem?_indexedPeripheralWord
      (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc) i₁
    change pre[j]? = _ at hi
    change pre[j + 1]? = _ at hi₁
    rw [hi] at hj
    rw [hi₁] at hj₁
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hj hj₁
    rw [← hj.1, ← hj₁.1]
    intro heq
    have hval := congrArg Fin.val heq
    simp [i, i₁] at hval
  · intro j mu g hjlen hj
    have hjlt : j < k := by
      have := lt_length_of_getElem?_eq_some hj
      simpa [pre] using this
    let i : Fin k := ⟨j, hjlt⟩
    have hi := getElem?_indexedPeripheralWord
      (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc) i
    change pre[j]? = _ at hi
    rw [hi] at hj
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hj
    rw [← hj.1]
    intro heq
    have hval := congrArg Fin.val heq
    simp [i] at hval
    have hprelen : pre.length = k := by simp [pre]
    rw [hprelen] at hjlen
    omega
  · intro mu g hj
    have h0 := getElem?_indexedPeripheralWord
      (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc)
      ⟨0, hk⟩
    change pre[0]? = _ at h0
    rw [h0] at hj
    simp only [Option.some.injEq, RelLetter.comp.injEq] at hj
    rw [← hj.1]
    intro heq
    have hval := congrArg Fin.val heq
    simp at hval
    omega

end HullSC
end GroupApproximation
