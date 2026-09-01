import GroupApproximation.GGT.HullYiCyclicProductAssembly
import GroupApproximation.GGT.HullYiCyclicOrientation
import GroupApproximation.GGT.DGOLemma421Statement
import GroupApproximation.GGT.HullSCRelatorSeparation2ConeOff

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
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

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

/-- Admissibility for the ambient-index form. -/
theorem isLetter_indexedPeripheralWord {k : ℕ} {Λ : Type w}
    (D : RelGenSet G Λ) (index : Fin k → Λ) (a : Fin k → G)
    (ha : ∀ i, a i ∈ D.fam (index i)) :
    ∀ c ∈ indexedPeripheralWord index a, D.IsLetter c := by
  intro c hc
  obtain ⟨i, rfl⟩ := exists_eq_comp_of_mem_indexedPeripheralWord index a hc
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

omit [Group G] in
/-- Splitting the finite cyclic word immediately before its last letter gives
the prefix used by `blockWord` followed by the distinguished closing letter. -/
theorem finPeripheralWord_eq_init_append_last {k : ℕ}
    (a : Fin (k + 1) → G) :
    finPeripheralWord a =
      indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
          (fun i : Fin k ↦ a i.castSucc) ++
        [RelLetter.comp (Fin.last k) (a (Fin.last k))] := by
  apply List.ext_getElem?
  intro q
  by_cases hq : q < k
  · have hfull := getElem?_indexedPeripheralWord id a
      ⟨q, lt_trans hq (Nat.lt_succ_self k)⟩
    have hpre := getElem?_indexedPeripheralWord
      (fun i : Fin k ↦ i.castSucc) (fun i : Fin k ↦ a i.castSucc) ⟨q, hq⟩
    rw [finPeripheralWord, hfull,
      List.getElem?_append_left (by simpa using hq), hpre]
    rfl
  · by_cases hqk : q = k
    · subst q
      have hfull := getElem?_indexedPeripheralWord id a
        ⟨k, Nat.lt_succ_self k⟩
      rw [finPeripheralWord, hfull,
        List.getElem?_append_right (by simp), length_indexedPeripheralWord]
      have heq : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = Fin.last k :=
        Fin.ext rfl
      simp [heq]
    · have hqbig : k + 1 ≤ q := by omega
      have hleft : (finPeripheralWord a)[q]? = none := by
        apply List.getElem?_eq_none
        simp
        omega
      have hright :
          (indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
              (fun i : Fin k ↦ a i.castSucc) ++
            [RelLetter.comp (Fin.last k) (a (Fin.last k))])[q]? = none := by
        apply List.getElem?_eq_none
        simp
        omega
      rw [hleft, hright]

/-- The value of the prefix followed by the distinguished last letter is the
ordered cyclic product. -/
theorem listVal_init_mul_last_eq_orderedFinProduct {k : ℕ}
    (a : Fin (k + 1) → G) :
    RelLetter.listVal
        (indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
          (fun i : Fin k ↦ a i.castSucc)) *
      a (Fin.last k) = orderedFinProduct a := by
  have hsplit := congrArg RelLetter.listVal
    (finPeripheralWord_eq_init_append_last a)
  rw [listVal_append, listVal_finPeripheralWord,
    OsinComponents.listVal_cons, RelLetter.listVal_nil,
    RelLetter.val, mul_one] at hsplit
  exact hsplit.symm

/-! ## The direct DGO 4.21(b) call site -/

/-- The word consisting of `n` copies of one full cyclic peripheral run. -/
def cyclicPeripheralPowerWord {k : ℕ} (a : Fin (k + 1) → G) (n : ℕ) :
    List (RelLetter G (Fin (k + 1))) :=
  OsinComponents.blockWord (Fin.last k)
    (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
    (a (Fin.last k)) n

/-- The concrete relative word used at the 4.21(b) call site spells the
corresponding natural power of Hull's ordered cyclic product. -/
@[simp] theorem listVal_cyclicPeripheralPowerWord {k : ℕ}
    (a : Fin (k + 1) → G) (n : ℕ) :
    RelLetter.listVal (cyclicPeripheralPowerWord a n) =
      orderedFinProduct a ^ n := by
  rw [cyclicPeripheralPowerWord, listVal_blockWord]
  rw [listVal_init_mul_last_eq_orderedFinProduct]

/-- Reading the entire concrete cyclic path from `v` ends at `v` times the
corresponding power of the ordered product. -/
@[simp] theorem vertex_length_cyclicPeripheralPowerWord {k : ℕ}
    (v : G) (a : Fin (k + 1) → G) (n : ℕ) :
    vertex v (cyclicPeripheralPowerWord a n)
        (cyclicPeripheralPowerWord a n).length =
      v * orderedFinProduct a ^ n := by
  rw [vertex_length, listVal_cyclicPeripheralPowerWord]

/-- At a cycle boundary, the path vertex is the corresponding natural power
of the ordered product. -/
theorem vertex_cycleBoundary_cyclicPeripheralPowerWord {k q n : ℕ}
    (v : G) (a : Fin (k + 1) → G) (hqn : q ≤ n) :
    vertex v (cyclicPeripheralPowerWord a n) (q * (k + 1)) =
      v * orderedFinProduct a ^ q := by
  have hv := vertex_blockWordAppend_block (Fin.last k)
    (indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
      (fun i : Fin k ↦ a i.castSucc))
    (a (Fin.last k)) v ([] : List (RelLetter G (Fin (k + 1)))) hqn
  rw [listVal_init_mul_last_eq_orderedFinProduct] at hv
  simpa [cyclicPeripheralPowerWord] using hv

omit [Group G] in
@[simp] theorem length_cyclicPeripheralPowerWord {k : ℕ}
    (a : Fin (k + 1) → G) (n : ℕ) :
    (cyclicPeripheralPowerWord a n).length = n * (k + 1) := by
  simp [cyclicPeripheralPowerWord]

omit [Group G] in
/-- The peripheral index at position `j` is `j mod (k+1)`.  This is the exact
cyclic-index bridge used to read the component sequence returned by 4.21(b). -/
theorem getElem?_cyclicPeripheralPowerWord {k n j : ℕ}
    (a : Fin (k + 1) → G)
    (hj : j < (cyclicPeripheralPowerWord a n).length) :
    (cyclicPeripheralPowerWord a n)[j]? =
      some (RelLetter.comp
        ⟨j % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩
        (a ⟨j % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩)) := by
  have hj' : j < n * (k + 1) := by simpa using hj
  obtain ⟨t, r, rfl, htn, hr⟩ := exists_block_decomp k hj'
  by_cases hrk : r < k
  · have hidx : t * (k + 1) + r =
        t * ((indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
          (fun i : Fin k ↦ a i.castSucc)).length + 1) + r := by simp
    rw [hidx, cyclicPeripheralPowerWord,
      getElem?_blockWord_pre (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) htn (by simpa using hrk)]
    rw [getElem?_indexedPeripheralWord
      (fun i : Fin k ↦ i.castSucc) (fun i : Fin k ↦ a i.castSucc) ⟨r, hrk⟩]
    simp only [length_indexedPeripheralWord]
    have hmod : (t * (k + 1) + r) % (k + 1) = r := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
    simp only [hmod]
    have hfin : (⟨r, hrk⟩ : Fin k).castSucc =
        ⟨r, hr⟩ := Fin.ext rfl
    rw [hfin]
  · have hrEq : r = k := by omega
    subst r
    have hidx : t * (k + 1) + k =
        t * ((indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
          (fun i : Fin k ↦ a i.castSucc)).length + 1) +
            (indexedPeripheralWord (fun i : Fin k ↦ i.castSucc)
              (fun i : Fin k ↦ a i.castSucc)).length := by simp
    rw [hidx, cyclicPeripheralPowerWord,
      getElem?_blockWord_comp (Fin.last k)
        (indexedPeripheralWord (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc))
        (a (Fin.last k)) htn]
    simp only [length_indexedPeripheralWord]
    have hmod : (t * (k + 1) + k) % (k + 1) = k := by
      simp [Nat.add_mod, Nat.mod_eq_of_lt (Nat.lt_succ_self k)]
    simp only [hmod]
    have hfin : Fin.last k =
        ⟨k, Nat.lt_succ_self k⟩ := Fin.ext rfl
    rw [hfin]

omit [Group G] in
/-- Every component returned by 4.21(b) on the cyclic word carries the index
predicted by its start position modulo the cycle length. -/
theorem componentIndex_cyclicPeripheralPowerWord {k n i q : ℕ}
    (a : Fin (k + 1) → G) {lam : Fin (k + 1)}
    (hcomp : IsComp lam (cyclicPeripheralPowerWord a n) i q) :
    lam = ⟨i % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩ := by
  obtain ⟨hiq, hq, hall, -, -⟩ := hcomp
  have hi : i < (cyclicPeripheralPowerWord a n).length := lt_of_lt_of_le hiq hq
  have hof : ((cyclicPeripheralPowerWord a n)[i]'hi).IsCompOf lam :=
    hall i le_rfl hiq hi
  obtain ⟨g, hg⟩ := getElem?_comp_of_isCompOf hi hof
  have hexact := getElem?_cyclicPeripheralPowerWord a hi
  rw [hexact] at hg
  simp only [Option.some.injEq, RelLetter.comp.injEq] at hg
  exact hg.1.symm

omit [Group G] in
/-- Since the cyclic peripheral word contains no base letters, the separator
between two consecutive distinguished components supplied by DGO 4.21(b)
cannot be an `X`-edge: it is a trivial path. -/
theorem eq_of_baseEdgeOrTrivial_cyclicPeripheralPowerWord {k n q i : ℕ}
    (a : Fin (k + 1) → G)
    (h : BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n) q i) :
    i = q := by
  rcases h with h | ⟨x, hi, hx⟩
  · exact h
  · exact False.elim
      (getElem?_blockWord_ne_base (Fin.last k)
        (getElem?_indexedPeripheralWord_ne_base
          (fun r : Fin k ↦ r.castSucc) (fun r : Fin k ↦ a r.castSucc))
        (a (Fin.last k)) n q x (by
          simpa [cyclicPeripheralPowerWord] using hx))

/-- Consecutive components supplied by DGO 4.21(b) on the cyclic peripheral
word advance through the peripheral factors in their natural cyclic order. -/
theorem cyclicSucc_componentIndex_of_consecutiveMatches
    (D : RelGenSet G (Fin (k + 1))) (hk : 1 ≤ k)
    (a : Fin (k + 1) → G) (n K : ℕ)
    (ip kp : ℕ → ℕ) (lam : ℕ → Fin (k + 1))
    (hcomp : ∀ t : ℕ, t < K →
      IsComp (lam t) (cyclicPeripheralPowerWord a n) (ip t) (kp t))
    (hstep : ∀ t : ℕ, t + 1 < K →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kp t) (ip (t + 1))) :
    ∀ t : ℕ, t + 1 < K → lam (t + 1) = cyclicSucc (lam t) := by
  intro t ht
  have hkp : kp t = ip t + 1 :=
    isComp_succ_of_isWThree
      (isWThree_blockWord_finPeripheralWord D hk a n)
      (hcomp t (by omega))
  have hip : ip (t + 1) = kp t :=
    eq_of_baseEdgeOrTrivial_cyclicPeripheralPowerWord a (hstep t ht)
  have hlam := componentIndex_cyclicPeripheralPowerWord a (hcomp t (by omega))
  have hlam1 := componentIndex_cyclicPeripheralPowerWord a (hcomp (t + 1) ht)
  rw [hlam, hlam1]
  apply Fin.ext
  simp [cyclicSucc, hip, hkp, Nat.add_mod]

/-- The starts of a consecutive matched run on the all-peripheral cyclic word
are consecutive natural positions, not merely strictly increasing positions. -/
theorem componentStart_eq_add_of_consecutiveMatches
    (D : RelGenSet G (Fin (k + 1))) (hk : 1 ≤ k)
    (a : Fin (k + 1) → G) (n K : ℕ)
    (ip kp : ℕ → ℕ) (lam : ℕ → Fin (k + 1))
    (hcomp : ∀ t : ℕ, t < K →
      IsComp (lam t) (cyclicPeripheralPowerWord a n) (ip t) (kp t))
    (hstep : ∀ t : ℕ, t + 1 < K →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kp t) (ip (t + 1))) :
    ∀ t : ℕ, t < K → ip t = ip 0 + t := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
      have hprev : t < K := by omega
      have hkp : kp t = ip t + 1 :=
        isComp_succ_of_isWThree
          (isWThree_blockWord_finPeripheralWord D hk a n)
          (hcomp t hprev)
      rw [eq_of_baseEdgeOrTrivial_cyclicPeripheralPowerWord a
        (hstep t (by omega)), hkp, ih hprev]
      omega

/-- A run of twice the cycle length contains a full naturally indexed cycle.
The offset is read directly from the first component's position, so no choice
or cyclic reindexing hypothesis is hidden in the statement. -/
theorem exists_naturallyIndexedCycle_of_consecutiveMatches
    (D : RelGenSet G (Fin (k + 1))) (hk : 1 ≤ k)
    (a : Fin (k + 1) → G) (n : ℕ)
    (ip kp : ℕ → ℕ) (lam : ℕ → Fin (k + 1))
    (hcomp : ∀ t : ℕ, t < 2 * (k + 1) + 1 →
      IsComp (lam t) (cyclicPeripheralPowerWord a n) (ip t) (kp t))
    (hstep : ∀ t : ℕ, t + 1 < 2 * (k + 1) + 1 →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kp t) (ip (t + 1))) :
    ∃ r : ℕ, r ≤ k + 1 ∧
      ∀ i : Fin (k + 1), lam (r + i.val) = i := by
  let m := k + 1
  let r := m - ip 0 % m
  have hm : 0 < m := by simp [m]
  have hr : r ≤ m := Nat.sub_le _ _
  refine ⟨r, by simpa [m] using hr, ?_⟩
  intro i
  have hri : r + i.val < 2 * (k + 1) + 1 := by
    have hi := i.isLt
    simp only [m] at hr
    omega
  have hstart := componentStart_eq_add_of_consecutiveMatches
    D hk a n (2 * (k + 1) + 1) ip kp lam hcomp hstep (r + i.val) hri
  have hindex := componentIndex_cyclicPeripheralPowerWord a (hcomp (r + i.val) hri)
  rw [hindex]
  apply Fin.ext
  change ip (r + i.val) % m = i.val
  rw [hstart]
  have hmod : ip 0 % m < m := Nat.mod_lt _ hm
  have hdiv : m * (ip 0 / m) + ip 0 % m = ip 0 := Nat.div_add_mod _ _
  have hsum : ip 0 + (r + i.val) = m * (ip 0 / m) + m + i.val := by
    dsimp [r]
    omega
  rw [hsum]
  have hi : i.val < m := by simpa [m] using i.isLt
  simpa [Nat.add_mod] using Nat.mod_eq_of_lt hi

/-- The connector labels at two consecutive matched components satisfy the
literal endpoint recurrence.  For two cyclic words with letters `a` and `b`,
the next connector is obtained by multiplying the current one by
`(a i)⁻¹` on the left and `b i` on the right. -/
theorem connector_succ_eq_of_consecutiveMatches
    (D : RelGenSet G (Fin (k + 1))) (hk : 1 ≤ k)
    (a b : Fin (k + 1) → G) (n K : ℕ) (vp vq : G)
    (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Fin (k + 1))
    (hcompA : ∀ t : ℕ, t < K →
      IsComp (lam t) (cyclicPeripheralPowerWord a n) (ip t) (kp t))
    (hcompB : ∀ t : ℕ, t < K →
      IsComp (lam t) (cyclicPeripheralPowerWord b n) (iq t) (kq t))
    (hstepA : ∀ t : ℕ, t + 1 < K →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kp t) (ip (t + 1)))
    (hstepB : ∀ t : ℕ, t + 1 < K →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord b n)
        (kq t) (iq (t + 1))) :
    ∀ t : ℕ, t + 1 < K →
      (vertex vp (cyclicPeripheralPowerWord a n) (ip (t + 1)))⁻¹ *
          vertex vq (cyclicPeripheralPowerWord b n) (iq (t + 1)) =
        (a (lam t))⁻¹ *
          ((vertex vp (cyclicPeripheralPowerWord a n) (ip t))⁻¹ *
            vertex vq (cyclicPeripheralPowerWord b n) (iq t)) *
          b (lam t) := by
  intro t ht
  have hcA := hcompA t (by omega)
  have hcB := hcompB t (by omega)
  have hkp : kp t = ip t + 1 :=
    isComp_succ_of_isWThree
      (isWThree_blockWord_finPeripheralWord D hk a n) hcA
  have hkq : kq t = iq t + 1 :=
    isComp_succ_of_isWThree
      (isWThree_blockWord_finPeripheralWord D hk b n) hcB
  have hip : ip (t + 1) = ip t + 1 := by
    rw [eq_of_baseEdgeOrTrivial_cyclicPeripheralPowerWord a (hstepA t ht), hkp]
  have hiq : iq (t + 1) = iq t + 1 := by
    rw [eq_of_baseEdgeOrTrivial_cyclicPeripheralPowerWord b (hstepB t ht), hkq]
  have hiplt : ip t < (cyclicPeripheralPowerWord a n).length :=
    lt_of_lt_of_le hcA.1 hcA.2.1
  have hiqlt : iq t < (cyclicPeripheralPowerWord b n).length :=
    lt_of_lt_of_le hcB.1 hcB.2.1
  have hindexA := componentIndex_cyclicPeripheralPowerWord a hcA
  have hindexB := componentIndex_cyclicPeripheralPowerWord b hcB
  have hgetA := getElem?_cyclicPeripheralPowerWord a hiplt
  have hgetB := getElem?_cyclicPeripheralPowerWord b hiqlt
  rw [← hindexA] at hgetA
  rw [← hindexB] at hgetB
  have hletterA :
      (cyclicPeripheralPowerWord a n)[ip t]'hiplt =
        RelLetter.comp (lam t) (a (lam t)) := by
    rw [List.getElem?_eq_getElem hiplt] at hgetA
    exact Option.some.inj hgetA
  have hletterB :
      (cyclicPeripheralPowerWord b n)[iq t]'hiqlt =
        RelLetter.comp (lam t) (b (lam t)) := by
    rw [List.getElem?_eq_getElem hiqlt] at hgetB
    exact Option.some.inj hgetB
  have hvA := vertex_succ (cyclicPeripheralPowerWord a n) vp (ip t) hiplt
  have hvB := vertex_succ (cyclicPeripheralPowerWord b n) vq (iq t) hiqlt
  rw [hletterA] at hvA
  rw [hletterB] at hvB
  rw [hip, hiq, hvA, hvB]
  simp only [RelLetter.val]
  group

/-- A sufficiently long self-match of the cyclic word produces exactly the
finite connector array consumed by Hull's post-matching algebra: the initial
connector for factor `i` lies in that factor, and its terminal connector is
conjugation by the `i`-th cyclic letter. -/
theorem exists_fullCycleConnectorData_of_consecutiveSelfMatches
    (D : RelGenSet G (Fin (k + 1))) (hk : 1 ≤ k)
    (a : Fin (k + 1) → G) (n : ℕ) (vp vq : G)
    (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Fin (k + 1))
    (hcompA : ∀ t : ℕ, t < 2 * (k + 1) + 1 →
      IsComp (lam t) (cyclicPeripheralPowerWord a n) (ip t) (kp t))
    (hcompB : ∀ t : ℕ, t < 2 * (k + 1) + 1 →
      IsComp (lam t) (cyclicPeripheralPowerWord a n) (iq t) (kq t))
    (hstepA : ∀ t : ℕ, t + 1 < 2 * (k + 1) + 1 →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kp t) (ip (t + 1)))
    (hstepB : ∀ t : ℕ, t + 1 < 2 * (k + 1) + 1 →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kq t) (iq (t + 1)))
    (hmem : ∀ t : ℕ, t < 2 * (k + 1) + 1 →
      (vertex vp (cyclicPeripheralPowerWord a n) (ip t))⁻¹ *
        vertex vq (cyclicPeripheralPowerWord a n) (iq t) ∈ D.fam (lam t)) :
    ∃ (r : ℕ) (c : Fin (k + 2) → G), r ≤ k + 1 ∧
      (∀ i : Fin (k + 1), lam (r + i.val) = i) ∧
      (∀ i : Fin (k + 1), c i.castSucc ∈ D.fam i) ∧
      (∀ i : Fin (k + 1),
        c i.succ = (a i)⁻¹ * c i.castSucc * a i) ∧
      ∀ j : Fin (k + 2),
        c j =
          (vertex vp (cyclicPeripheralPowerWord a n) (ip (r + j.val)))⁻¹ *
            vertex vq (cyclicPeripheralPowerWord a n) (iq (r + j.val)) := by
  obtain ⟨r, hr, hlam⟩ := exists_naturallyIndexedCycle_of_consecutiveMatches
    D hk a n ip kp lam hcompA hstepA
  let c : Fin (k + 2) → G := fun j ↦
    (vertex vp (cyclicPeripheralPowerWord a n) (ip (r + j.val)))⁻¹ *
      vertex vq (cyclicPeripheralPowerWord a n) (iq (r + j.val))
  refine ⟨r, c, hr, hlam, ?_, ?_, ?_⟩
  · intro i
    have hri : r + i.val < 2 * (k + 1) + 1 := by
      have hi := i.isLt
      omega
    have hm := hmem (r + i.val) hri
    rw [hlam i] at hm
    exact hm
  · intro i
    have hri : r + i.val + 1 < 2 * (k + 1) + 1 := by
      have hi := i.isLt
      omega
    have hrec := connector_succ_eq_of_consecutiveMatches
      D hk a a n (2 * (k + 1) + 1) vp vq ip kp iq kq lam
      hcompA hcompB hstepA hstepB (r + i.val) hri
    rw [hlam i] at hrec
    simpa [c, Nat.add_assoc] using hrec
  · intro j
    rfl

/-- With the second copy of the cyclic word based at `t`, the aligned first
connector also gives Hull's prefix equation.  The prefix is trivial here;
the two integer exponents record the cycle boundaries at which the matched
components begin. -/
theorem exists_fullCycleMatchData_of_consecutiveSelfMatches
    (D : RelGenSet G (Fin (k + 1))) (hk : 1 ≤ k)
    (a : Fin (k + 1) → G) (n : ℕ) (t : G)
    (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Fin (k + 1))
    (hcompA : ∀ s : ℕ, s < 2 * (k + 1) + 1 →
      IsComp (lam s) (cyclicPeripheralPowerWord a n) (ip s) (kp s))
    (hcompB : ∀ s : ℕ, s < 2 * (k + 1) + 1 →
      IsComp (lam s) (cyclicPeripheralPowerWord a n) (iq s) (kq s))
    (hstepA : ∀ s : ℕ, s + 1 < 2 * (k + 1) + 1 →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kp s) (ip (s + 1)))
    (hstepB : ∀ s : ℕ, s + 1 < 2 * (k + 1) + 1 →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kq s) (iq (s + 1)))
    (hmem : ∀ s : ℕ, s < 2 * (k + 1) + 1 →
      (vertex 1 (cyclicPeripheralPowerWord a n) (ip s))⁻¹ *
        vertex t (cyclicPeripheralPowerWord a n) (iq s) ∈ D.fam (lam s)) :
    ∃ (l m : ℤ) (c : Fin (k + 2) → G),
      (∀ i : Fin (k + 1), c i.castSucc ∈ D.fam i) ∧
      (∀ i : Fin (k + 1),
        c i.succ = (a i)⁻¹ * c i.castSucc * a i) ∧
      t = orderedFinProduct a ^ l * c 0 * orderedFinProduct a ^ (-m) := by
  obtain ⟨r, c, hr, hlam, hcmem, hcrec, hcdef⟩ :=
    exists_fullCycleConnectorData_of_consecutiveSelfMatches
      D hk a n 1 t ip kp iq kq lam hcompA hcompB hstepA hstepB hmem
  let cycleLength := k + 1
  have hcycle : 0 < cycleLength := by simp [cycleLength]
  have hrange : r < 2 * (k + 1) + 1 := by omega
  have hlam0 : lam r = 0 := by
    simpa using hlam (0 : Fin (k + 1))
  have hindexA := componentIndex_cyclicPeripheralPowerWord a (hcompA r hrange)
  have hindexB := componentIndex_cyclicPeripheralPowerWord a (hcompB r hrange)
  have hmodA : ip r % cycleLength = 0 := by
    have hval := congrArg Fin.val hindexA
    have hz : 0 = ip r % cycleLength := by
      simpa [hlam0, cycleLength] using hval
    exact hz.symm
  have hmodB : iq r % cycleLength = 0 := by
    have hval := congrArg Fin.val hindexB
    have hz : 0 = iq r % cycleLength := by
      simpa [hlam0, cycleLength] using hval
    exact hz.symm
  have hipBoundary : ip r = (ip r / cycleLength) * cycleLength := by
    have hdiv := Nat.div_add_mod (ip r) cycleLength
    rw [hmodA, add_zero] at hdiv
    exact hdiv.symm.trans (Nat.mul_comm _ _)
  have hiqBoundary : iq r = (iq r / cycleLength) * cycleLength := by
    have hdiv := Nat.div_add_mod (iq r) cycleLength
    rw [hmodB, add_zero] at hdiv
    exact hdiv.symm.trans (Nat.mul_comm _ _)
  have hiplt : ip r < n * cycleLength := by
    have hc := hcompA r hrange
    simpa [cycleLength] using
      (lt_of_lt_of_le hc.1 hc.2.1)
  have hiqlt : iq r < n * cycleLength := by
    have hc := hcompB r hrange
    simpa [cycleLength] using
      (lt_of_lt_of_le hc.1 hc.2.1)
  have hpcycles : ip r / cycleLength < n :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hiplt)
  have hqcycles : iq r / cycleLength < n :=
    Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hiqlt)
  have hvA :
      vertex 1 (cyclicPeripheralPowerWord a n) (ip r) =
        orderedFinProduct a ^ (ip r / cycleLength) := by
    rw [hipBoundary]
    simpa [cycleLength] using
      vertex_cycleBoundary_cyclicPeripheralPowerWord
        (v := (1 : G)) a (Nat.le_of_lt hpcycles)
  have hvB :
      vertex t (cyclicPeripheralPowerWord a n) (iq r) =
        t * orderedFinProduct a ^ (iq r / cycleLength) := by
    rw [hiqBoundary]
    simpa [cycleLength] using
      vertex_cycleBoundary_cyclicPeripheralPowerWord
        (v := t) a (Nat.le_of_lt hqcycles)
  have hc0 := hcdef (0 : Fin (k + 2))
  simp only [Fin.val_zero, Nat.add_zero] at hc0
  rw [hvA, hvB] at hc0
  refine ⟨(ip r / cycleLength : ℕ), (iq r / cycleLength : ℕ), c,
    hcmem, hcrec, ?_⟩
  rw [hc0]
  simp only [zpow_natCast, zpow_neg]
  group

/-- The same endpoint in the literal `HasConsecutiveComponentMatch` shape for
the cone-off by the detector elementary closures.  The prefix is `1`; unlike
the downstream definition, no arbitrary prefix datum is needed at this
basepoint choice. -/
theorem exists_hasConsecutiveComponentMatchData_of_consecutiveSelfMatches
    (A : Alphabet G) (f a : Fin (k + 1) → G) (hk : 1 ≤ k)
    (n : ℕ) (t : G)
    (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Fin (k + 1))
    (hcompA : ∀ s : ℕ, s < 2 * (k + 1) + 1 →
      IsComp (lam s) (cyclicPeripheralPowerWord a n) (ip s) (kp s))
    (hcompB : ∀ s : ℕ, s < 2 * (k + 1) + 1 →
      IsComp (lam s) (cyclicPeripheralPowerWord a n) (iq s) (kq s))
    (hstepA : ∀ s : ℕ, s + 1 < 2 * (k + 1) + 1 →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kp s) (ip (s + 1)))
    (hstepB : ∀ s : ℕ, s + 1 < 2 * (k + 1) + 1 →
      BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
        (kq s) (iq (s + 1)))
    (hmem : ∀ s : ℕ, s < 2 * (k + 1) + 1 →
      (vertex 1 (cyclicPeripheralPowerWord a n) (ip s))⁻¹ *
          vertex t (cyclicPeripheralPowerWord a n) (iq s) ∈
        elementaryClosure (f (lam s))) :
    ∃ (l m : ℤ) (p : G) (c : Fin (k + 2) → G),
      (∀ i : Fin (k + 1), c i.castSucc ∈ elementaryClosure (f i)) ∧
      (∀ i : Fin (k + 1),
        c i.succ = (a i)⁻¹ * c i.castSucc * a i) ∧
      t = orderedFinProduct a ^ l * p * c 0 * p⁻¹ *
        orderedFinProduct a ^ (-m) := by
  obtain ⟨l, m, c, hcmem, hcrec, ht⟩ :=
    exists_fullCycleMatchData_of_consecutiveSelfMatches
      (coneOffFamily A (fun i ↦ elementaryClosure (f i))) hk
      a n t ip kp iq kq lam hcompA hcompB hstepA hstepB hmem
  refine ⟨l, m, 1, c, hcmem, hcrec, ?_⟩
  simpa using ht

/-- **The literal cyclic-product specialization of DGO Lemma 4.21(b).**

The constants `C,R` are chosen in exactly the order of the printed lemma.
After that, any two sufficiently long powers of deep cyclic peripheral words
whose endpoints are oriented `eps`-close have `K` consecutive component
matches.  All admissibility and (W1)--(W3) premises are discharged here from
the concrete word; the conclusion is DGO's raw component-index output, with no
connector or non-commensurability conclusion inserted. -/
theorem exists_consecutiveMatches_cyclicPeripheralPowerWord_of_dgoLemma421b
    (h421b : DGOLemma421b.{u, 0}) {k : ℕ}
    (D : RelGenSet G (Fin (k + 1)))
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ (Cayley D.alphabet))
    (hk : 1 ≤ k) (eps : ℝ) (K : ℕ) (heps : 0 < eps) (hK : 0 < K) :
    ∃ C R : ℕ, 0 < R ∧
      ∀ (a b : Fin (k + 1) → G),
        (∀ i, a i ∈ D.fam i) → (∀ i, b i ∈ D.fam i) →
        (∀ i, a i ∉ D.relBall i C) →
        (∀ i, b i ∉ D.relBall i C) →
        ∀ n : ℕ, R ≤ n * (k + 1) → ∀ vp vq : G,
        (wordDist D.alphabet.carrier vp vq : ℝ) ≤ eps →
        (wordDist D.alphabet.carrier
          (vertex vp (cyclicPeripheralPowerWord a n)
            (cyclicPeripheralPowerWord a n).length)
          (vertex vq (cyclicPeripheralPowerWord b n)
            (cyclicPeripheralPowerWord b n).length) : ℝ) ≤ eps →
        ∃ (ip kp iq kq : ℕ → ℕ) (lam : ℕ → Fin (k + 1)),
          (∀ t : ℕ, t < K →
            IsComp (lam t) (cyclicPeripheralPowerWord a n) (ip t) (kp t)) ∧
          (∀ t : ℕ, t < K →
            IsComp (lam t) (cyclicPeripheralPowerWord b n) (iq t) (kq t)) ∧
          (∀ t : ℕ, t + 1 < K →
            BaseEdgeOrTrivial (cyclicPeripheralPowerWord a n)
              (kp t) (ip (t + 1))) ∧
          (∀ t : ℕ, t + 1 < K →
            BaseEdgeOrTrivial (cyclicPeripheralPowerWord b n)
              (kq t) (iq (t + 1))) ∧
          ∀ t : ℕ, t < K →
            (vertex vp (cyclicPeripheralPowerWord a n) (ip t))⁻¹ *
              vertex vq (cyclicPeripheralPowerWord b n) (iq t)
                ∈ D.fam (lam t) := by
  obtain ⟨C, hraw⟩ := h421b G (Fin (k + 1)) D hhyp
  obtain ⟨R, hR, hmatch⟩ := hraw eps K heps hK
  refine ⟨C, R, hR, ?_⟩
  intro a b ha hb hdeepA hdeepB n hn vp vq hstart hend
  apply hmatch vp vq (cyclicPeripheralPowerWord a n)
    (cyclicPeripheralPowerWord b n)
  · apply isLetter_of_mem_blockWord D (Fin.last k)
    · exact isLetter_indexedPeripheralWord D
        (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc) (fun i ↦ ha i.castSucc)
    · exact ha (Fin.last k)
  · apply isLetter_of_mem_blockWord D (Fin.last k)
    · exact isLetter_indexedPeripheralWord D
        (fun i ↦ i.castSucc) (fun i ↦ b i.castSucc) (fun i ↦ hb i.castSucc)
    · exact hb (Fin.last k)
  · exact isWOne_blockWord_finPeripheralWord a n
  · exact isWTwo_blockWord_finPeripheralWord D a hdeepA n
  · exact isWThree_blockWord_finPeripheralWord D hk a n
  · exact isWOne_blockWord_finPeripheralWord b n
  · exact isWTwo_blockWord_finPeripheralWord D b hdeepB n
  · exact isWThree_blockWord_finPeripheralWord D hk b n
  · simpa using hn
  · exact hstart
  · exact hend

/-- DGO 4.21(b) supplies the complete `HasConsecutiveComponentMatch` payload
for an element which normalizes a positive power of the cyclic product without
reversing its orientation.  The 4.21 depth constant is chosen before the
letters, while the path-length threshold is allowed to depend on `t`, exactly
as in Hull's proof. -/
theorem exists_depth_hasConsecutiveComponentMatchData_of_positiveNormalizer
    (h421b : DGOLemma421b.{u, 0}) (A : Alphabet G)
    (f : Fin (k + 1) → G) (hk : 1 ≤ k)
    (hhyp : ∃ δ : ℝ, IsHyperbolicSpace δ
      (Cayley (coneOffFamily A (fun i ↦ elementaryClosure (f i))).alphabet)) :
    ∃ C : ℕ, ∀ (a : Fin (k + 1) → G),
      (∀ i, a i ∈ elementaryClosure (f i)) →
      (∀ i, a i ∉
        (coneOffFamily A (fun i ↦ elementaryClosure (f i))).relBall i C) →
      ∀ (t : G) (q : ℕ), 0 < q →
      t * orderedFinProduct a ^ q * t⁻¹ = orderedFinProduct a ^ q →
      ∃ (l m : ℤ) (p : G) (c : Fin (k + 2) → G),
        (∀ i : Fin (k + 1), c i.castSucc ∈ elementaryClosure (f i)) ∧
        (∀ i : Fin (k + 1),
          c i.succ = (a i)⁻¹ * c i.castSucc * a i) ∧
        t = orderedFinProduct a ^ l * p * c 0 * p⁻¹ *
          orderedFinProduct a ^ (-m) := by
  let D : RelGenSet G (Fin (k + 1)) :=
    coneOffFamily A (fun i ↦ elementaryClosure (f i))
  obtain ⟨C, hraw⟩ := h421b G (Fin (k + 1)) D hhyp
  refine ⟨C, ?_⟩
  intro a ha hdeep t q hq hnormalize
  let K := 2 * (k + 1) + 1
  let eps : ℝ := (wordDist D.alphabet.carrier 1 t : ℝ) + 1
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  have hK : 0 < K := by simp [K]
  obtain ⟨R, hR, hmatch⟩ := hraw eps K heps hK
  let N := q * R
  have hcycle : 0 < k + 1 := by omega
  have hlength : R ≤ N * (k + 1) := by
    dsimp [N]
    exact (Nat.le_mul_of_pos_left R hq).trans
      (Nat.le_mul_of_pos_right (q * R) hcycle)
  have hnormalizeN :
      t * orderedFinProduct a ^ N * t⁻¹ = orderedFinProduct a ^ N := by
    dsimp [N]
    calc
      t * orderedFinProduct a ^ (q * R) * t⁻¹ =
          (t * orderedFinProduct a ^ q * t⁻¹) ^ R := by
            rw [pow_mul, conj_pow]
      _ = (orderedFinProduct a ^ q) ^ R := by rw [hnormalize]
      _ = orderedFinProduct a ^ (q * R) := by rw [pow_mul]
  have hcommuteN :
      t * orderedFinProduct a ^ N = orderedFinProduct a ^ N * t := by
    calc
      t * orderedFinProduct a ^ N =
          (t * orderedFinProduct a ^ N * t⁻¹) * t := by group
      _ = orderedFinProduct a ^ N * t := by rw [hnormalizeN]
  have hstart : (wordDist D.alphabet.carrier 1 t : ℝ) ≤ eps := by
    dsimp [eps]
    norm_num
  have hend :
      (wordDist D.alphabet.carrier
        (vertex 1 (cyclicPeripheralPowerWord a N)
          (cyclicPeripheralPowerWord a N).length)
        (vertex t (cyclicPeripheralPowerWord a N)
          (cyclicPeripheralPowerWord a N).length) : ℝ) ≤ eps := by
    simp only [vertex_length_cyclicPeripheralPowerWord, one_mul]
    have hdist := wordDist_left_invariant D.alphabet.carrier
      (orderedFinProduct a ^ N)⁻¹ (orderedFinProduct a ^ N)
      (t * orderedFinProduct a ^ N)
    have hsimp :
        (orderedFinProduct a ^ N)⁻¹ * (t * orderedFinProduct a ^ N) = t := by
      rw [hcommuteN]
      group
    rw [inv_mul_cancel, hsimp] at hdist
    calc
      (wordDist D.alphabet.carrier (orderedFinProduct a ^ N)
          (t * orderedFinProduct a ^ N) : ℝ) =
          (wordDist D.alphabet.carrier 1 t : ℝ) := by
            exact_mod_cast hdist.symm
      _ ≤ eps := hstart
  have hletter : ∀ c ∈ cyclicPeripheralPowerWord a N, D.IsLetter c := by
    apply isLetter_of_mem_blockWord D (Fin.last k)
    · exact isLetter_indexedPeripheralWord D
        (fun i ↦ i.castSucc) (fun i ↦ a i.castSucc)
        (fun i ↦ ha i.castSucc)
    · exact ha (Fin.last k)
  obtain ⟨ip, kp, iq, kq, lam, hcompA, hcompB, hstepA, hstepB, hmem⟩ :=
    hmatch 1 t (cyclicPeripheralPowerWord a N)
      (cyclicPeripheralPowerWord a N)
      hletter hletter
      (isWOne_blockWord_finPeripheralWord a N)
      (isWTwo_blockWord_finPeripheralWord D a hdeep N)
      (isWThree_blockWord_finPeripheralWord D hk a N)
      (isWOne_blockWord_finPeripheralWord a N)
      (isWTwo_blockWord_finPeripheralWord D a hdeep N)
      (isWThree_blockWord_finPeripheralWord D hk a N)
      (by simpa using hlength) hstart hend
  exact exists_hasConsecutiveComponentMatchData_of_consecutiveSelfMatches
    A f a hk N t ip kp iq kq lam hcompA hcompB hstepA hstepB hmem

end HullSC
end GroupApproximation
